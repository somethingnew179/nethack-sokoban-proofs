import NetHack.Soko22Hazard87.AndIntroBlocks0067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro17000 (p : Pattern) (ha : d8013 p = 1) (hb : d107483 p = 1) : d111249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d107483 q = 1) : d111234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16997 q ha hb
    | true =>
      simp only [d7989, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d107483 q = 1) : d111235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8010 q = 1) (hb : d107483 q = 1) : d111246 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8010, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8011 q = 1) (hb : d107483 q = 1) : d111247 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8011, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8012 q = 1) (hb : d107483 q = 1) : d111248 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8012, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8013 q = 1) (hb : d107483 q = 1) : d111249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8013, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17001 (p : Pattern) (ha : d85616 p = 1) (hb : d107483 p = 1) : d111255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7999 q = 1) (hb : d107483 q = 1) : d111244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16998 q ha hb
    | true =>
      simp only [d7999, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16999 q ha hb
  have h2 (q : Pattern) (ha : d85612 q = 1) (hb : d107483 q = 1) : d111245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85612, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8014 q = 1) (hb : d107483 q = 1) : d111250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17000 q ha hb
    | true =>
      simp only [d8014, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8015 q = 1) (hb : d107483 q = 1) : d111251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8015, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d107483 q = 1) : d111252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85613, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d107483 q = 1) : d111253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d107483 q = 1) : d111254 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d107483 q = 1) : d111255 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17002 (p : Pattern) (ha : d85622 p = 1) (hb : d107483 p = 1) : d111261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d107483 q = 1) : d111151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16976 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d107483 q = 1) : d111152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d107483 q = 1) : d111160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16976 q ha hb
    | true =>
      simp only [d7904, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16978 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d107483 q = 1) : d111161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d107483 q = 1) : d111162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85600 q = 1) (hb : d107483 q = 1) : d111214 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16987 q ha hb
    | true =>
      simp only [d85600, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16994 q ha hb
  have h7 (q : Pattern) (ha : d7971 q = 1) (hb : d107483 q = 1) : d111216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16979 q ha hb
    | true =>
      simp only [d7971, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16969 q ha hb
  have h8 (q : Pattern) (ha : d85601 q = 1) (hb : d107483 q = 1) : d111217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85601, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85602 q = 1) (hb : d107483 q = 1) : d111218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85602, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85603 q = 1) (hb : d107483 q = 1) : d111219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85603, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85607 q = 1) (hb : d107483 q = 1) : d111223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85607, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16995 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d107483 q = 1) : d11800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16970 q ha hb
  have h13 (q : Pattern) (ha : d85608 q = 1) (hb : d107483 q = 1) : d111224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85608, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85609 q = 1) (hb : d107483 q = 1) : d111225 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85609, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85610 q = 1) (hb : d107483 q = 1) : d111226 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85610, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85611 q = 1) (hb : d107483 q = 1) : d111227 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85611, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85617 q = 1) (hb : d107483 q = 1) : d111256 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85617, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17001 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d107483 q = 1) : d11893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16973 q ha hb
  have h19 (q : Pattern) (ha : d85618 q = 1) (hb : d107483 q = 1) : d111257 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85618, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85619 q = 1) (hb : d107483 q = 1) : d111258 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85619, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85620 q = 1) (hb : d107483 q = 1) : d111259 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85620, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85621 q = 1) (hb : d107483 q = 1) : d111260 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85621, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85622 q = 1) (hb : d107483 q = 1) : d111261 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85622, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17003 (p : Pattern) (ha : d85628 p = 1) (hb : d107483 p = 1) : d111267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d107483 q = 1) : d111262 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17002 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d107483 q = 1) : d111263 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d107483 q = 1) : d111264 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d107483 q = 1) : d111265 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d107483 q = 1) : d111266 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d107483 q = 1) : d111267 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17004 (p : Pattern) (ha : d2096 p = 1) (hb : d107483 p = 1) : d11922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2090 q = 1) (hb : d85721 q = 1) : d11916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2095 q = 1) (hb : d107483 q = 1) : d11921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d107483, d11921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2095, d107483, d11921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2096 q = 1) (hb : d107483 q = 1) : d11922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2096, d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17005 (p : Pattern) (ha : d2106 p = 1) (hb : d107483 p = 1) : d11932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d107483 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d107483 q = 1) : d11931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d107483 q = 1) : d11932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17006 (p : Pattern) (ha : d2116 p = 1) (hb : d107483 p = 1) : d11942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d107483 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d107483 q = 1) : d11931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d107483 q = 1) : d11942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17007 (p : Pattern) (ha : d2316 p = 1) (hb : d107483 p = 1) : d12062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d107483 q = 1) : d12051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17005 q ha hb
    | true =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d107483 q = 1) : d12052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d107483 q = 1) : d12053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d107483 q = 1) : d12054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d107483 q = 1) : d12055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d107483 q = 1) : d12057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17006 q ha hb
    | true =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d107483 q = 1) : d12058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d107483 q = 1) : d12059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d107483 q = 1) : d12060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d107483 q = 1) : d12061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d107483 q = 1) : d12062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17008 (p : Pattern) (ha : d2325 p = 1) (hb : d107483 p = 1) : d12071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d107483 q = 1) : d12057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17006 q ha hb
    | true =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d107483 q = 1) : d12058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d107483 q = 1) : d12059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d107483 q = 1) : d12060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d107483 q = 1) : d12061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d107483 q = 1) : d12071 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17009 (p : Pattern) (ha : d2385 p = 1) (hb : d107483 p = 1) : d12102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2375 q = 1) (hb : d85721 q = 1) : d12092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2384 q = 1) (hb : d107483 q = 1) : d12101 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d107483, d12101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2384, d107483, d12101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2385 q = 1) (hb : d107483 q = 1) : d12102 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2385, d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro17010 (p : Pattern) (ha : d2452 p = 1) (hb : d107483 p = 1) : d12158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d107483 q = 1) : d12103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17009 q ha hb
    | true =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d107483 q = 1) : d12104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d107483 q = 1) : d12155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d12155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d12155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d107483 q = 1) : d12156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d107483 q = 1) : d12157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d107483 q = 1) : d12158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17011 (p : Pattern) (ha : d2458 p = 1) (hb : d107483 p = 1) : d12164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d107483 q = 1) : d12159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17010 q ha hb
    | true =>
      simp only [d2453, d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d107483 q = 1) : d12160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d107483 q = 1) : d12161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d107483 q = 1) : d12162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d107483 q = 1) : d12163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d107483 q = 1) : d12164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17012 (p : Pattern) (ha : d8037 p = 1) (hb : d107483 p = 1) : d111273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2089 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8036 q = 1) (hb : d107483 q = 1) : d111272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8036, d107483, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8037 q = 1) (hb : d107483 q = 1) : d111273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8037, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17013 (p : Pattern) (ha : d8043 p = 1) (hb : d107483 p = 1) : d111279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d107483 q = 1) : d111278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8043 q = 1) (hb : d107483 q = 1) : d111279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17014 (p : Pattern) (ha : d8049 p = 1) (hb : d107483 p = 1) : d111285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17013 q ha hb
    | true =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17005 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8049 q = 1) (hb : d107483 q = 1) : d111285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17015 (p : Pattern) (ha : d8052 p = 1) (hb : d107483 p = 1) : d111288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d107483 q = 1) : d111278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8052 q = 1) (hb : d107483 q = 1) : d111288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8052, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17016 (p : Pattern) (ha : d8058 p = 1) (hb : d107483 p = 1) : d111294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17013 q ha hb
    | true =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17005 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8053 q = 1) (hb : d107483 q = 1) : d111289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17015 q ha hb
    | true =>
      simp only [d8053, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17006 q ha hb
  have h7 (q : Pattern) (ha : d8054 q = 1) (hb : d107483 q = 1) : d111290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8055 q = 1) (hb : d107483 q = 1) : d111291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8055, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8056 q = 1) (hb : d107483 q = 1) : d111292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8057 q = 1) (hb : d107483 q = 1) : d111293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8058 q = 1) (hb : d107483 q = 1) : d111294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8058, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17017 (p : Pattern) (ha : d8125 p = 1) (hb : d107483 p = 1) : d111350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d107483 q = 1) : d111280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17013 q ha hb
    | true =>
      simp only [d8044, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17005 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d107483 q = 1) : d111281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d107483 q = 1) : d111282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d107483 q = 1) : d111283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d107483 q = 1) : d111284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d107483 q = 1) : d12051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17005 q ha hb
    | true =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d107483 q = 1) : d12052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d107483 q = 1) : d12053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d107483 q = 1) : d12054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d107483 q = 1) : d12055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8125 q = 1) (hb : d107483 q = 1) : d111350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8125, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17018 (p : Pattern) (ha : d2129 p = 1) (hb : d107483 p = 1) : d11955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d107483 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d107483 q = 1) : d11954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d107483 q = 1) : d11955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17019 (p : Pattern) (ha : d2139 p = 1) (hb : d107483 p = 1) : d11965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d107483 q = 1) : d11963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d107483 q = 1) : d11964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d107483 q = 1) : d11965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17020 (p : Pattern) (ha : d8063 p = 1) (hb : d107483 p = 1) : d111299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d107483 q = 1) : d111298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8063 q = 1) (hb : d107483 q = 1) : d111299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17021 (p : Pattern) (ha : d8070 p = 1) (hb : d107483 p = 1) : d111306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d107483 q = 1) : d111304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d107483 q = 1) : d111305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8070 q = 1) (hb : d107483 q = 1) : d111306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17022 (p : Pattern) (ha : d8075 p = 1) (hb : d107483 p = 1) : d111311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2149 q = 1) : d2149 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2150 q = 1) (hb : d85721 q = 1) : d11969 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d85721, d11969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2150, d85721, d11969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2151 q = 1) (hb : d85721 q = 1) : d11970 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d11970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d11970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2152 q = 1) (hb : d85721 q = 1) : d11971 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d11971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d11971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2153 q = 1) (hb : d85721 q = 1) : d11972 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d11972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2153, d11972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8074 q = 1) (hb : d107483 q = 1) : d111310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8074, d107483, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8074, d107483, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8075 q = 1) (hb : d107483 q = 1) : d111311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8075, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8075, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17023 (p : Pattern) (ha : d8081 p = 1) (hb : d107483 p = 1) : d111317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d107483 q = 1) : d111312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17022 q ha hb
    | true =>
      simp only [d8076, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d107483 q = 1) : d111313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d107483 q = 1) : d111314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d107483 q = 1) : d111315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d107483 q = 1) : d111316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8081 q = 1) (hb : d107483 q = 1) : d111317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17024 (p : Pattern) (ha : d8096 p = 1) (hb : d107483 p = 1) : d111323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d107483 q = 1) : d111320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d107483 q = 1) : d111321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d107483 q = 1) : d111322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8096 q = 1) (hb : d107483 q = 1) : d111323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8096, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17025 (p : Pattern) (ha : d85637 p = 1) (hb : d107483 p = 1) : d111329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d107483 q = 1) : d111300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17020 q ha hb
    | true =>
      simp only [d8064, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17018 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d107483 q = 1) : d111301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d107483 q = 1) : d111302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d107483 q = 1) : d111303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d107483 q = 1) : d111307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17021 q ha hb
    | true =>
      simp only [d8071, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17019 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d107483 q = 1) : d111308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d107483 q = 1) : d111309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d107483 q = 1) : d111318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17023 q ha hb
    | true =>
      simp only [d8082, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17013 q ha hb
  have h9 (q : Pattern) (ha : d85633 q = 1) (hb : d107483 q = 1) : d111319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85633, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8097 q = 1) (hb : d107483 q = 1) : d111324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17024 q ha hb
    | true =>
      simp only [d8097, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8098 q = 1) (hb : d107483 q = 1) : d111325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8098, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85634 q = 1) (hb : d107483 q = 1) : d111326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85634, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85635 q = 1) (hb : d107483 q = 1) : d111327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85635, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85636 q = 1) (hb : d107483 q = 1) : d111328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85636, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85637 q = 1) (hb : d107483 q = 1) : d111329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17026 (p : Pattern) (ha : d2282 p = 1) (hb : d107483 p = 1) : d12027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d107483 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d107483 q = 1) : d11954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d107483 q = 1) : d12027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17027 (p : Pattern) (ha : d2288 p = 1) (hb : d107483 p = 1) : d12033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d107483 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d107483 q = 1) : d11963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d107483 q = 1) : d11964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d107483 q = 1) : d12033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17028 (p : Pattern) (ha : d8103 p = 1) (hb : d107483 p = 1) : d111330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d107483 q = 1) : d111277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d107483 q = 1) : d111298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8103 q = 1) (hb : d107483 q = 1) : d111330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8103, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17029 (p : Pattern) (ha : d8108 p = 1) (hb : d107483 p = 1) : d111335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d107483 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17004 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d107483 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d107483 q = 1) : d111276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d107483 q = 1) : d111304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d107483 q = 1) : d111305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8108 q = 1) (hb : d107483 q = 1) : d111335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8108, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17030 (p : Pattern) (ha : d8112 p = 1) (hb : d107483 p = 1) : d111339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d107483 q = 1) : d111312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17022 q ha hb
    | true =>
      simp only [d8076, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d107483 q = 1) : d111313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8078 q = 1) (hb : d107483 q = 1) : d111314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8078, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8079 q = 1) (hb : d107483 q = 1) : d111315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8079, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8080 q = 1) (hb : d107483 q = 1) : d111316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8080, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8112 q = 1) (hb : d107483 q = 1) : d111339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8112, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17031 (p : Pattern) (ha : d8117 p = 1) (hb : d107483 p = 1) : d111342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d107483 q = 1) : d111274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17012 q ha hb
    | true =>
      simp only [d8038, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d107483 q = 1) : d111275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d107483 q = 1) : d111320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8093, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d107483 q = 1) : d111321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d107483 q = 1) : d111322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8117 q = 1) (hb : d107483 q = 1) : d111342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8117, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17032 (p : Pattern) (ha : d85642 p = 1) (hb : d107483 p = 1) : d111348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d107483 q = 1) : d111300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17020 q ha hb
    | true =>
      simp only [d8064, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17018 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d107483 q = 1) : d111301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d107483 q = 1) : d111302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d107483 q = 1) : d111303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d107483 q = 1) : d111307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17021 q ha hb
    | true =>
      simp only [d8071, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17019 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d107483 q = 1) : d111308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d107483 q = 1) : d111309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8082 q = 1) (hb : d107483 q = 1) : d111318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17023 q ha hb
    | true =>
      simp only [d8082, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17013 q ha hb
  have h9 (q : Pattern) (ha : d85633 q = 1) (hb : d107483 q = 1) : d111319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85633, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8097 q = 1) (hb : d107483 q = 1) : d111324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17024 q ha hb
    | true =>
      simp only [d8097, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8098 q = 1) (hb : d107483 q = 1) : d111325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8098, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85634 q = 1) (hb : d107483 q = 1) : d111326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85634, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85635 q = 1) (hb : d107483 q = 1) : d111327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85635, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85636 q = 1) (hb : d107483 q = 1) : d111328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85636, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8104 q = 1) (hb : d107483 q = 1) : d111331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17028 q ha hb
    | true =>
      simp only [d8104, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17026 q ha hb
  have h16 (q : Pattern) (ha : d8105 q = 1) (hb : d107483 q = 1) : d111332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8106 q = 1) (hb : d107483 q = 1) : d111333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8106, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8107 q = 1) (hb : d107483 q = 1) : d111334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8109 q = 1) (hb : d107483 q = 1) : d111336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17029 q ha hb
    | true =>
      simp only [d8109, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17027 q ha hb
  have h20 (q : Pattern) (ha : d8110 q = 1) (hb : d107483 q = 1) : d111337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8111 q = 1) (hb : d107483 q = 1) : d111338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8111, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8113 q = 1) (hb : d107483 q = 1) : d111340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17030 q ha hb
    | true =>
      simp only [d8113, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17015 q ha hb
  have h23 (q : Pattern) (ha : d85638 q = 1) (hb : d107483 q = 1) : d111341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85638, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8118 q = 1) (hb : d107483 q = 1) : d111343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17031 q ha hb
    | true =>
      simp only [d8118, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8119 q = 1) (hb : d107483 q = 1) : d111344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8119, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85639 q = 1) (hb : d107483 q = 1) : d111345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d85639, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d85640 q = 1) (hb : d107483 q = 1) : d111346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85640, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85641 q = 1) (hb : d107483 q = 1) : d111347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85641, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85642 q = 1) (hb : d107483 q = 1) : d111348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85642, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro17033 (p : Pattern) (ha : d85649 p = 1) (hb : d107483 p = 1) : d111357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8113 q = 1) (hb : d107483 q = 1) : d111340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17030 q ha hb
    | true =>
      simp only [d8113, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17015 q ha hb
  have h2 (q : Pattern) (ha : d85638 q = 1) (hb : d107483 q = 1) : d111341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85638, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8118 q = 1) (hb : d107483 q = 1) : d111343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17031 q ha hb
    | true =>
      simp only [d8118, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8119 q = 1) (hb : d107483 q = 1) : d111344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8119, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d107483 q = 1) : d111345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85639, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d107483 q = 1) : d111355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d107483 q = 1) : d111356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d107483 q = 1) : d111357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17034 (p : Pattern) (ha : d8139 p = 1) (hb : d107483 p = 1) : d111364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2345 q = 1) : d2345 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2352 q = 1) (hb : d85721 q = 1) : d12077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d85721, d12077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2352, d85721, d12077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2353 q = 1) (hb : d85721 q = 1) : d12078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d12078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d12078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2354 q = 1) (hb : d85721 q = 1) : d12079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d12079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d12079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2360 q = 1) (hb : d85721 q = 1) : d12083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d12083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2360, d12083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8138 q = 1) (hb : d107483 q = 1) : d111363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8138, d107483, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8138, d107483, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8139 q = 1) (hb : d107483 q = 1) : d111364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8139, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8139, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17035 (p : Pattern) (ha : d8143 p = 1) (hb : d107483 p = 1) : d111368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2370 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8142 q = 1) (hb : d107483 q = 1) : d111367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8142, d107483, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8143 q = 1) (hb : d107483 q = 1) : d111368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8143, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17036 (p : Pattern) (ha : d8149 p = 1) (hb : d107483 p = 1) : d111374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8140 q = 1) (hb : d107483 q = 1) : d111365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17034 q ha hb
    | true =>
      simp only [d8140, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8141 q = 1) (hb : d107483 q = 1) : d111366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8141, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8144 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17035 q ha hb
    | true =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8145 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8146 q = 1) (hb : d107483 q = 1) : d111371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8146, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8147 q = 1) (hb : d107483 q = 1) : d111372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8147, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8148 q = 1) (hb : d107483 q = 1) : d111373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8148, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8149 q = 1) (hb : d107483 q = 1) : d111374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8149, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17037 (p : Pattern) (ha : d8153 p = 1) (hb : d107483 p = 1) : d111378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17035 q ha hb
    | true =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d107483 q = 1) : d12103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17009 q ha hb
    | true =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d107483 q = 1) : d12104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8150 q = 1) (hb : d107483 q = 1) : d111375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8150, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8151 q = 1) (hb : d107483 q = 1) : d111376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8151, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8152 q = 1) (hb : d107483 q = 1) : d111377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8152, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8153 q = 1) (hb : d107483 q = 1) : d111378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8153, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro17038 (p : Pattern) (ha : d8168 p = 1) (hb : d107483 p = 1) : d111384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d107483 q = 1) : d111369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17035 q ha hb
    | true =>
      simp only [d8144, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d107483 q = 1) : d111370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8165 q = 1) (hb : d107483 q = 1) : d111381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8165, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8165, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8166 q = 1) (hb : d107483 q = 1) : d111382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8166, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8166, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8167 q = 1) (hb : d107483 q = 1) : d111383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8167, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8167, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8168 q = 1) (hb : d107483 q = 1) : d111384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8168, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8168, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17039 (p : Pattern) (ha : d85659 p = 1) (hb : d107483 p = 1) : d111390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8154 q = 1) (hb : d107483 q = 1) : d111379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17036 q ha hb
    | true =>
      simp only [d8154, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17037 q ha hb
  have h2 (q : Pattern) (ha : d85655 q = 1) (hb : d107483 q = 1) : d111380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85655, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8169 q = 1) (hb : d107483 q = 1) : d111385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17038 q ha hb
    | true =>
      simp only [d8169, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8170 q = 1) (hb : d107483 q = 1) : d111386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8170, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d107483 q = 1) : d111387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85656, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d107483 q = 1) : d111388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d107483 q = 1) : d111389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d107483 q = 1) : d111390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17040 (p : Pattern) (ha : d85665 p = 1) (hb : d107483 p = 1) : d111396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d107483 q = 1) : d111286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17014 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d107483 q = 1) : d111287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d107483 q = 1) : d111295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17014 q ha hb
    | true =>
      simp only [d8059, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17016 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d107483 q = 1) : d111296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d107483 q = 1) : d111297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85643 q = 1) (hb : d107483 q = 1) : d111349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17025 q ha hb
    | true =>
      simp only [d85643, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17032 q ha hb
  have h7 (q : Pattern) (ha : d8126 q = 1) (hb : d107483 q = 1) : d111351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17017 q ha hb
    | true =>
      simp only [d8126, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17007 q ha hb
  have h8 (q : Pattern) (ha : d85644 q = 1) (hb : d107483 q = 1) : d111352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85644, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85645 q = 1) (hb : d107483 q = 1) : d111353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85645, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d85646 q = 1) (hb : d107483 q = 1) : d111354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85646, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85650 q = 1) (hb : d107483 q = 1) : d111358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85650, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17033 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d107483 q = 1) : d12072 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17008 q ha hb
  have h13 (q : Pattern) (ha : d85651 q = 1) (hb : d107483 q = 1) : d111359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85651, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85652 q = 1) (hb : d107483 q = 1) : d111360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85652, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d85653 q = 1) (hb : d107483 q = 1) : d111361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85653, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d85654 q = 1) (hb : d107483 q = 1) : d111362 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85654, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85660 q = 1) (hb : d107483 q = 1) : d111391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85660, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17039 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d107483 q = 1) : d12165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17011 q ha hb
  have h19 (q : Pattern) (ha : d85661 q = 1) (hb : d107483 q = 1) : d111392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85661, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d85662 q = 1) (hb : d107483 q = 1) : d111393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85662, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d85663 q = 1) (hb : d107483 q = 1) : d111394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85663, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d85664 q = 1) (hb : d107483 q = 1) : d111395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85664, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d85665 q = 1) (hb : d107483 q = 1) : d111396 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85665, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17041 (p : Pattern) (ha : d85671 p = 1) (hb : d107483 p = 1) : d111402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d107483 q = 1) : d111397 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17040 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d107483 q = 1) : d111398 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d107483 q = 1) : d111399 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d107483 q = 1) : d111400 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d107483 q = 1) : d111401 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d107483 q = 1) : d111402 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17042 (p : Pattern) (ha : d85677 p = 1) (hb : d107483 p = 1) : d111408 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d107483 q = 1) : d110869 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16853 q ha hb
    | true =>
      simp only [d85506, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16889 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d107483 q = 1) : d111001 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16927 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d107483 q = 1) : d111002 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d107483 q = 1) : d111134 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16965 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d107483 q = 1) : d111135 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d107483 q = 1) : d111136 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d107483 q = 1) : d111268 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17003 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d107483 q = 1) : d111269 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d107483 q = 1) : d111270 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d107483 q = 1) : d111271 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d107483 q = 1) : d111403 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17041 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d107483 q = 1) : d111404 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d107483 q = 1) : d111405 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d107483 q = 1) : d111406 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d107483 q = 1) : d111407 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d107483 q = 1) : d111408 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro17043 (p : Pattern) (ha : d85683 p = 1) (hb : d107483 p = 1) : d111414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d107483 q = 1) : d111409 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17042 q ha hb
    | true =>
      simp only [d85678, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d107483 q = 1) : d111410 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d107483 q = 1) : d111411 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d107483 q = 1) : d111412 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d107483 q = 1) : d111413 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d107483 q = 1) : d111414 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17044 (p : Pattern) (ha : d85689 p = 1) (hb : d107483 p = 1) : d111420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d107483 q = 1) : d111415 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17043 q ha hb
    | true =>
      simp only [d85684, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d107483 q = 1) : d111416 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d107483 q = 1) : d111417 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d107483 q = 1) : d111418 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d107483 q = 1) : d111419 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d107483 q = 1) : d111420 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17045 (p : Pattern) (ha : d85695 p = 1) (hb : d107483 p = 1) : d111426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d107483 q = 1) : d111421 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17044 q ha hb
    | true =>
      simp only [d85690, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d107483 q = 1) : d111422 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d107483 q = 1) : d111423 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d107483 q = 1) : d111424 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d107483 q = 1) : d111425 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d107483 q = 1) : d111426 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17046 (p : Pattern) (ha : d85701 p = 1) (hb : d107483 p = 1) : d111432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d107483 q = 1) : d111427 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17045 q ha hb
    | true =>
      simp only [d85696, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d107483 q = 1) : d111428 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d107483 q = 1) : d111429 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d107483 q = 1) : d111430 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d107483 q = 1) : d111431 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d107483 q = 1) : d111432 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17047 (p : Pattern) (ha : d85707 p = 1) (hb : d107483 p = 1) : d111438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d107483 q = 1) : d111433 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17046 q ha hb
    | true =>
      simp only [d85702, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d107483 q = 1) : d111434 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d107483 q = 1) : d111435 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d107483 q = 1) : d111436 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d107483 q = 1) : d111437 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d107483 q = 1) : d111438 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17048 (p : Pattern) (ha : d85713 p = 1) (hb : d107483 p = 1) : d111444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d107483 q = 1) : d111439 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17047 q ha hb
    | true =>
      simp only [d85708, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d107483 q = 1) : d111440 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d107483 q = 1) : d111441 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d107483 q = 1) : d111442 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d107483 q = 1) : d111443 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d107483 q = 1) : d111444 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17049 (p : Pattern) (ha : d85719 p = 1) (hb : d107483 p = 1) : d111450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d107483 q = 1) : d111445 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17048 q ha hb
    | true =>
      simp only [d85714, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d107483 q = 1) : d111446 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d107483 q = 1) : d111447 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d107483 q = 1) : d111448 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d107483 q = 1) : d111449 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d107483 q = 1) : d111450 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro17050 (p : Pattern) (ha : d107491 p = 1) (hb : d110577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10652 q = 1) (hb : d107489 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107490 q = 1) (hb : d110576 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107490, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107490, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107491 q = 1) (hb : d110577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107491, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107491, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17051 (p : Pattern) (ha : d107497 p = 1) (hb : d110583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107496 q = 1) (hb : d110582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107496, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107496, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107497 q = 1) (hb : d110583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107497, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107497, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17052 (p : Pattern) (ha : d107503 p = 1) (hb : d110589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d110585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107499, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d110586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d110587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d110588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107503 q = 1) (hb : d110589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107503, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107503, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17053 (p : Pattern) (ha : d107504 p = 1) (hb : d110590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107496 q = 1) (hb : d110582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107496, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107496, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107504 q = 1) (hb : d110590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107504, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107504, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17054 (p : Pattern) (ha : d107510 p = 1) (hb : d110596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d110585 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107499, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d110586 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d110587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d110588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d107505 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
    | true =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107506 q = 1) (hb : d110592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107506, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d107507 q = 1) (hb : d110593 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107507, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d107508 q = 1) (hb : d110594 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107508, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d107508, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107509 q = 1) (hb : d110595 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107509, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d107509, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107510 q = 1) (hb : d110596 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107510, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107510, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17055 (p : Pattern) (ha : d107517 p = 1) (hb : d110603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107505 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
    | true =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107506 q = 1) (hb : d110592 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107506, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
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
  have h6 (q : Pattern) (ha : d107507 q = 1) (hb : d110593 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107507, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107515 q = 1) (hb : d110601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107515, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107515, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107516 q = 1) (hb : d110602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107516, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107516, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107517 q = 1) (hb : d110603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107517, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107517, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17056 (p : Pattern) (ha : d107528 p = 1) (hb : d110610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10689 q = 1) (hb : d107526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107527 q = 1) (hb : d110609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107527, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107527, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107528 q = 1) (hb : d110610 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107528, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107528, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17057 (p : Pattern) (ha : d107534 p = 1) (hb : d110616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17056 q ha hb
    | true =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107531 q = 1) (hb : d110613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107531, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107531, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107532 q = 1) (hb : d110614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107532, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107532, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107533 q = 1) (hb : d110615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107533, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107533, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107534 q = 1) (hb : d110616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107534, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107534, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17058 (p : Pattern) (ha : d107540 p = 1) (hb : d110622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107535 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17057 q ha hb
    | true =>
      simp only [d107535, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107536 q = 1) (hb : d110618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107536, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107536, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
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
  have h6 (q : Pattern) (ha : d107537 q = 1) (hb : d110619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107537, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107537, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107538 q = 1) (hb : d110620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107538, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107538, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107539 q = 1) (hb : d110621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107539, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107539, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107540 q = 1) (hb : d110622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107540, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107540, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17059 (p : Pattern) (ha : d107546 p = 1) (hb : d110628 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d107511 q = 1) (hb : d110597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107511, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17052 q ha hb
    | true =>
      simp only [d107511, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17054 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d107512 q = 1) (hb : d110598 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107512, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107512, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107513 q = 1) (hb : d110599 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107513, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107513, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107514 q = 1) (hb : d110600 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107514, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107514, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107518 q = 1) (hb : d110604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107518, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107518, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17055 q ha hb
  have h12 (q : Pattern) (ha : d107519 q = 1) (hb : d110605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107519, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107519, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107520 q = 1) (hb : d110606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107520, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107520, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107521 q = 1) (hb : d110607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107521, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107521, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107522 q = 1) (hb : d110608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107522, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107522, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107541 q = 1) (hb : d110623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107541, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107541, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17058 q ha hb
  have h17 (q : Pattern) (ha : d107542 q = 1) (hb : d110624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107542, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107542, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d107543 q = 1) (hb : d110625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107543, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107543, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107544 q = 1) (hb : d110626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107544, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d107544, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d107545 q = 1) (hb : d110627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107545, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107545, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107546 q = 1) (hb : d110628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107546, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107546, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro17060 (p : Pattern) (ha : d107556 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107556 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107556, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107556, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17061 (p : Pattern) (ha : d107563 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107505 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
    | true =>
      simp only [d107505, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d107559 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107559, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107559, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107560 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107560, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107560, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107561 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107561, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107561, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107562 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107562, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107562, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107563 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107563, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107563, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17062 (p : Pattern) (ha : d107568 p = 1) (hb : d110650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d110649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107568 q = 1) (hb : d110650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107568, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107568, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17063 (p : Pattern) (ha : d107575 p = 1) (hb : d110657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d110655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d110656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107575 q = 1) (hb : d110657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107575, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107575, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17064 (p : Pattern) (ha : d107584 p = 1) (hb : d110662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10745 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107489 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107583 q = 1) (hb : d110661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107583, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107583, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107584 q = 1) (hb : d110662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107584, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107584, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17065 (p : Pattern) (ha : d107590 p = 1) (hb : d110668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17064 q ha hb
    | true =>
      simp only [d107585, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d110665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d110666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d110667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107590 q = 1) (hb : d110668 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107590, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107590, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17066 (p : Pattern) (ha : d107596 p = 1) (hb : d110674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d110671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d110672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d110673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107596 q = 1) (hb : d110674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107596, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107596, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17067 (p : Pattern) (ha : d107602 p = 1) (hb : d110680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d110651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17062 q ha hb
    | true =>
      simp only [d107569, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d110652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d110653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d110654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d110658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17063 q ha hb
    | true =>
      simp only [d107576, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d110659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d110660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d110669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17065 q ha hb
    | true =>
      simp only [d107591, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d110670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d110675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17066 q ha hb
    | true =>
      simp only [d107597, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d110676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d110677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d110678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d110679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107602 q = 1) (hb : d110680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17068 (p : Pattern) (ha : d107603 p = 1) (hb : d110681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d110581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d110649 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107603 q = 1) (hb : d110681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107603, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107603, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17069 (p : Pattern) (ha : d107608 p = 1) (hb : d110686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d110580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d110655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d110656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107608 q = 1) (hb : d110686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107608, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107608, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17070 (p : Pattern) (ha : d107612 p = 1) (hb : d110690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17064 q ha hb
    | true =>
      simp only [d107585, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d110665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d110666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d110667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107612 q = 1) (hb : d110690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107612, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107612, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17071 (p : Pattern) (ha : d107615 p = 1) (hb : d110693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d110578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17050 q ha hb
    | true =>
      simp only [d107492, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d110579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d110671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d110672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d110673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107615 q = 1) (hb : d110693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107615, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107615, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17072 (p : Pattern) (ha : d107621 p = 1) (hb : d110699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d110651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17062 q ha hb
    | true =>
      simp only [d107569, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d110652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d110653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d110654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d110658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17063 q ha hb
    | true =>
      simp only [d107576, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d110659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d110660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d110669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17065 q ha hb
    | true =>
      simp only [d107591, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d110670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d110675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17066 q ha hb
    | true =>
      simp only [d107597, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d110676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d110677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d110678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d110679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107604 q = 1) (hb : d110682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107604, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17068 q ha hb
    | true =>
      simp only [d107604, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d107605 q = 1) (hb : d110683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107605, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107605, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107606 q = 1) (hb : d110684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107606, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107606, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107607 q = 1) (hb : d110685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107607, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107607, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107609 q = 1) (hb : d110687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107609, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17069 q ha hb
    | true =>
      simp only [d107609, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d107610 q = 1) (hb : d110688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107610, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107610, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107611 q = 1) (hb : d110689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107611, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107611, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107613 q = 1) (hb : d110691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17070 q ha hb
    | true =>
      simp only [d107613, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107614 q = 1) (hb : d110692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107614, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107616 q = 1) (hb : d110694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17071 q ha hb
    | true =>
      simp only [d107616, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107617 q = 1) (hb : d110695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107617, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107618 q = 1) (hb : d110696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107618, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107619 q = 1) (hb : d110697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107619, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107620 q = 1) (hb : d110698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107620, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107621 q = 1) (hb : d110699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107621, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17073 (p : Pattern) (ha : d107623 p = 1) (hb : d110701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17051 q ha hb
    | true =>
      simp only [d107498, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107623 q = 1) (hb : d110701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107623, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107623, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17074 (p : Pattern) (ha : d107630 p = 1) (hb : d110708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107613 q = 1) (hb : d110691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17070 q ha hb
    | true =>
      simp only [d107613, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17053 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d110692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107614, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107616 q = 1) (hb : d110694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17071 q ha hb
    | true =>
      simp only [d107616, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107617 q = 1) (hb : d110695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107617, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107618 q = 1) (hb : d110696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107628 q = 1) (hb : d110706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107629 q = 1) (hb : d110707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107630 q = 1) (hb : d110708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17075 (p : Pattern) (ha : d107641 p = 1) (hb : d110715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10817 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107526 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107640 q = 1) (hb : d110714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107640, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107640, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107641 q = 1) (hb : d110715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107641, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107641, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17076 (p : Pattern) (ha : d107647 p = 1) (hb : d110721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107642 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107642, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17075 q ha hb
    | true =>
      simp only [d107642, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107643 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107643, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107643, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107529 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17056 q ha hb
    | true =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107530 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107644 q = 1) (hb : d110718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107644, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107644, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107645 q = 1) (hb : d110719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107645, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107645, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107646 q = 1) (hb : d110720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107646, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107646, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107647 q = 1) (hb : d110721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107647, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107647, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17077 (p : Pattern) (ha : d107653 p = 1) (hb : d110727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d110611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17056 q ha hb
    | true =>
      simp only [d107529, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d110612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107650 q = 1) (hb : d110724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107650, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107650, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107651 q = 1) (hb : d110725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107651, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107651, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107652 q = 1) (hb : d110726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107652, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107652, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107653 q = 1) (hb : d110727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107653, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107653, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17078 (p : Pattern) (ha : d107659 p = 1) (hb : d110733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107648 q = 1) (hb : d110722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107648, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17076 q ha hb
    | true =>
      simp only [d107648, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d110723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107649, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107654 q = 1) (hb : d110728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107654, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17077 q ha hb
    | true =>
      simp only [d107654, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107655 q = 1) (hb : d110729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107655, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107655, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107656 q = 1) (hb : d110730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107657 q = 1) (hb : d110731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107658 q = 1) (hb : d110732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107659 q = 1) (hb : d110733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17079 (p : Pattern) (ha : d107665 p = 1) (hb : d110739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107557 q = 1) (hb : d110639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107557, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107557, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17060 q ha hb
  have h2 (q : Pattern) (ha : d107558 q = 1) (hb : d110640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107558, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107558, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107564 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107564, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17060 q ha hb
    | true =>
      simp only [d107564, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17061 q ha hb
  have h4 (q : Pattern) (ha : d107565 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107565, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107565, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107566 q = 1) (hb : d110648 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107566, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107566, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107622 q = 1) (hb : d110700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17067 q ha hb
    | true =>
      simp only [d107622, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17072 q ha hb
  have h7 (q : Pattern) (ha : d107624 q = 1) (hb : d110702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107624, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17073 q ha hb
    | true =>
      simp only [d107624, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d107625 q = 1) (hb : d110703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107625, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107626 q = 1) (hb : d110704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107626, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107627 q = 1) (hb : d110705 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107627, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107631 q = 1) (hb : d110709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107631, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17074 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d107632 q = 1) (hb : d110710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107632, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107633 q = 1) (hb : d110711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107633, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107634 q = 1) (hb : d110712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107634, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107635 q = 1) (hb : d110713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107635, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107660 q = 1) (hb : d110734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107660, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17078 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d107661 q = 1) (hb : d110735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107661, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107662 q = 1) (hb : d110736 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107662, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107663 q = 1) (hb : d110737 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107663, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107664 q = 1) (hb : d110738 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107664, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107665 q = 1) (hb : d110739 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107665, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17080 (p : Pattern) (ha : d107671 p = 1) (hb : d110745 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d107547 q = 1) (hb : d110629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107547, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107547, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17059 q ha hb
  have h6 (q : Pattern) (ha : d107548 q = 1) (hb : d110630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107548, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107548, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107549 q = 1) (hb : d110631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107549, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107549, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107550 q = 1) (hb : d110632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107550, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107550, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107551 q = 1) (hb : d110633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107551, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107551, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107666 q = 1) (hb : d110740 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107666, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17079 q ha hb
  have h11 (q : Pattern) (ha : d107667 q = 1) (hb : d110741 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107667, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107668 q = 1) (hb : d110742 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107668, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107669 q = 1) (hb : d110743 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107669, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107670 q = 1) (hb : d110744 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107670, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107671 q = 1) (hb : d110745 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107671, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17081 (p : Pattern) (ha : d107674 p = 1) (hb : d110662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10745 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107672 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107673 q = 1) (hb : d110661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107673, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107673, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107674 q = 1) (hb : d110662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107674, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107674, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17082 (p : Pattern) (ha : d107684 p = 1) (hb : d110749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d110748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107684 q = 1) (hb : d110749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107684, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107684, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17083 (p : Pattern) (ha : d107694 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
    | true =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107694 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107694, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107694, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17084 (p : Pattern) (ha : d107697 p = 1) (hb : d110758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d110748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107697 q = 1) (hb : d110758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107697, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107697, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17085 (p : Pattern) (ha : d107704 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
    | true =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107699 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17084 q ha hb
    | true =>
      simp only [d107699, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q hb ha
  have h7 (q : Pattern) (ha : d107700 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107700, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107700, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107701 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107701, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107701, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107702 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107702, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107702, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107703 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107703, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107703, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107704 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107704, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107704, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17086 (p : Pattern) (ha : d107709 p = 1) (hb : d110769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d110768 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107709 q = 1) (hb : d110769 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107709, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107709, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17087 (p : Pattern) (ha : d107718 p = 1) (hb : d110776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d110774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d110775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107718 q = 1) (hb : d110776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107718, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107718, d110776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17088 (p : Pattern) (ha : d107730 p = 1) (hb : d110781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10916 q = 1) (hb : d107725 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10917 q = 1) (hb : d107726 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10918 q = 1) (hb : d107727 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10919 q = 1) (hb : d107728 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107729 q = 1) (hb : d110780 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107729, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107729, d110780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107730 q = 1) (hb : d110781 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107730, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107730, d110781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17089 (p : Pattern) (ha : d107736 p = 1) (hb : d110787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d110782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17088 q ha hb
    | true =>
      simp only [d107731, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d110783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d110784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d110785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d110786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107736 q = 1) (hb : d110787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107736, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107736, d110787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17090 (p : Pattern) (ha : d107742 p = 1) (hb : d110793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d110790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d110791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d110792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107742 q = 1) (hb : d110793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107742, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107742, d110793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17091 (p : Pattern) (ha : d107748 p = 1) (hb : d110799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d110770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17086 q ha hb
    | true =>
      simp only [d107712, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15949 q hb ha
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d110771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d110772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d110773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d110777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17087 q ha hb
    | true =>
      simp only [d107722, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15951 q hb ha
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d110778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d110779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d110788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17089 q ha hb
    | true =>
      simp only [d107737, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d110789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d110794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17090 q ha hb
    | true =>
      simp only [d107743, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d110795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d110796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d110797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d110798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107748 q = 1) (hb : d110799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d110799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17092 (p : Pattern) (ha : d107749 p = 1) (hb : d110800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d110747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d110768 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107749 q = 1) (hb : d110800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107749, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107749, d110800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17093 (p : Pattern) (ha : d107755 p = 1) (hb : d110805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d110746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d110774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d110774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d110775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d110775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107755 q = 1) (hb : d110805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107755, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107755, d110805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17094 (p : Pattern) (ha : d107760 p = 1) (hb : d110809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d110782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17088 q ha hb
    | true =>
      simp only [d107731, d110782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d110783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d110783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d110784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d110784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d110785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d110785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d110786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d110786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107760 q = 1) (hb : d110809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107760, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107760, d110809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17095 (p : Pattern) (ha : d107763 p = 1) (hb : d110812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d110663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17081 q ha hb
    | true =>
      simp only [d107675, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d110664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d110790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d110790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d110791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d110791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d110792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d110792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107763 q = 1) (hb : d110812 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107763, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107763, d110812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17096 (p : Pattern) (ha : d107769 p = 1) (hb : d110818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d110770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17086 q ha hb
    | true =>
      simp only [d107712, d110770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15949 q hb ha
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d110771 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d110771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d110772 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d110772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d110773 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d110773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d110777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17087 q ha hb
    | true =>
      simp only [d107722, d110777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15951 q hb ha
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d110778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d110778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d110779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d110779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d110788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17089 q ha hb
    | true =>
      simp only [d107737, d110788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d110789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d110789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d110794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17090 q ha hb
    | true =>
      simp only [d107743, d110794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d110795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d110795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d110796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d110796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d110797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d110797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d110798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d110798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107751 q = 1) (hb : d110801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107751, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17092 q ha hb
    | true =>
      simp only [d107751, d110801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15957 q hb ha
  have h17 (q : Pattern) (ha : d107752 q = 1) (hb : d110802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107752, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107752, d110802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107753 q = 1) (hb : d110803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107753, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107753, d110803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107754 q = 1) (hb : d110804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107754, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107754, d110804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107757 q = 1) (hb : d110806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107757, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17093 q ha hb
    | true =>
      simp only [d107757, d110806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15959 q hb ha
  have h21 (q : Pattern) (ha : d107758 q = 1) (hb : d110807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107758, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107758, d110807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107759 q = 1) (hb : d110808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107759, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107759, d110808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107761 q = 1) (hb : d110810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17094 q ha hb
    | true =>
      simp only [d107761, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17084 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107762 q = 1) (hb : d110811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107762, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107764 q = 1) (hb : d110813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17095 q ha hb
    | true =>
      simp only [d107764, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107765 q = 1) (hb : d110814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107765, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107766 q = 1) (hb : d110815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107766, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107767 q = 1) (hb : d110816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107767, d110816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107768 q = 1) (hb : d110817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107768, d110817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107769 q = 1) (hb : d110818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107769, d110818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17097 (p : Pattern) (ha : d107776 p = 1) (hb : d110820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17082 q ha hb
    | true =>
      simp only [d107689, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q hb ha
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d107771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
    | true =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d107772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d107773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d107774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d107775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107776 q = 1) (hb : d110820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107776, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107776, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17098 (p : Pattern) (ha : d107789 p = 1) (hb : d110827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107761 q = 1) (hb : d110810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17094 q ha hb
    | true =>
      simp only [d107761, d110810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17084 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d110811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107762, d110811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107764 q = 1) (hb : d110813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17095 q ha hb
    | true =>
      simp only [d107764, d110813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107765 q = 1) (hb : d110814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107765, d110814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107766 q = 1) (hb : d110815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d110815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107787 q = 1) (hb : d110825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d110825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107788 q = 1) (hb : d110826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d110826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107789 q = 1) (hb : d110827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d110827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17099 (p : Pattern) (ha : d107802 p = 1) (hb : d110834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11013 q = 1) (hb : d107797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11014 q = 1) (hb : d107798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11015 q = 1) (hb : d107799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11016 q = 1) (hb : d107800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107801 q = 1) (hb : d110833 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107801, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107801, d110833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107802 q = 1) (hb : d110834 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107802, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107802, d110834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17100 (p : Pattern) (ha : d107807 p = 1) (hb : d110715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10817 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107805 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107806 q = 1) (hb : d110714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107806, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107806, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107807 q = 1) (hb : d110715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107807, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107807, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17101 (p : Pattern) (ha : d107813 p = 1) (hb : d110840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107803 q = 1) (hb : d110835 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107803, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17099 q ha hb
    | true =>
      simp only [d107803, d110835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107804 q = 1) (hb : d110836 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107804, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107804, d110836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107808 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17100 q ha hb
    | true =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107809 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107810 q = 1) (hb : d110837 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107810, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107810, d110837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107811 q = 1) (hb : d110838 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107811, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107811, d110838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107812 q = 1) (hb : d110839 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107812, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107812, d110839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107813 q = 1) (hb : d110840 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107813, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107813, d110840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17102 (p : Pattern) (ha : d107821 p = 1) (hb : d110844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17100 q ha hb
    | true =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d107816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15945 q ha hb
    | true =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d107817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107818 q = 1) (hb : d110841 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107818, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107818, d110841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107819 q = 1) (hb : d110842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107819, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107819, d110842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107820 q = 1) (hb : d110843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107820, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107820, d110843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107821 q = 1) (hb : d110844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107821, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107821, d110844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17103 (p : Pattern) (ha : d107832 p = 1) (hb : d110850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d110716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17100 q ha hb
    | true =>
      simp only [d107808, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d110717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107829 q = 1) (hb : d110847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107829, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107829, d110847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107830 q = 1) (hb : d110848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107830, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107830, d110848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107831 q = 1) (hb : d110849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107831, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107831, d110849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107832 q = 1) (hb : d110850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107832, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107832, d110850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17104 (p : Pattern) (ha : d107838 p = 1) (hb : d110856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107822 q = 1) (hb : d110845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107822, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17101 q ha hb
    | true =>
      simp only [d107822, d110845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17102 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d110846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107828, d110846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107833 q = 1) (hb : d110851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107833, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17103 q ha hb
    | true =>
      simp only [d107833, d110851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107834 q = 1) (hb : d110852 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107834, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107834, d110852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107835 q = 1) (hb : d110853 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d110853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107836 q = 1) (hb : d110854 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d110854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107837 q = 1) (hb : d110855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d110855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107838 q = 1) (hb : d110856 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d110856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17105 (p : Pattern) (ha : d107851 p = 1) (hb : d110862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107695 q = 1) (hb : d110756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107695, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107695, d110756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17083 q ha hb
  have h2 (q : Pattern) (ha : d107696 q = 1) (hb : d110757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107696, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107696, d110757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107705 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107705, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17083 q ha hb
    | true =>
      simp only [d107705, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17085 q ha hb
  have h4 (q : Pattern) (ha : d107706 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107706, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107706, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107707 q = 1) (hb : d110767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107707, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107707, d110767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107770 q = 1) (hb : d110819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17091 q ha hb
    | true =>
      simp only [d107770, d110819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17096 q ha hb
  have h7 (q : Pattern) (ha : d107783 q = 1) (hb : d110821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107783, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17097 q ha hb
    | true =>
      simp only [d107783, d110821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15943 q hb ha
  have h8 (q : Pattern) (ha : d107784 q = 1) (hb : d110822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107784, d110822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107785 q = 1) (hb : d110823 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107785, d110823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107786 q = 1) (hb : d110824 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107786, d110824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107790 q = 1) (hb : d110828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107790, d110828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17098 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15944 q ha hb
  have h13 (q : Pattern) (ha : d107793 q = 1) (hb : d110829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107793, d110829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107794 q = 1) (hb : d110830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107794, d110830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107795 q = 1) (hb : d110831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107795, d110831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107796 q = 1) (hb : d110832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107796, d110832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107839 q = 1) (hb : d110857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107839, d110857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17104 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15947 q ha hb
  have h19 (q : Pattern) (ha : d107847 q = 1) (hb : d110858 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107847, d110858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107848 q = 1) (hb : d110859 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107848, d110859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107849 q = 1) (hb : d110860 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107849, d110860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107850 q = 1) (hb : d110861 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107850, d110861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107851 q = 1) (hb : d110862 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107851, d110862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17106 (p : Pattern) (ha : d107857 p = 1) (hb : d110868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d110863 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d110863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17105 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d110864 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d110864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d110865 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d110865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d110866 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d110866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d110867 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d110867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d110868 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d110868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17107 (p : Pattern) (ha : d107868 p = 1) (hb : d110871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11102 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107866 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107867 q = 1) (hb : d110870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107867, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107867, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107868 q = 1) (hb : d110871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107868, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107868, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17108 (p : Pattern) (ha : d107878 p = 1) (hb : d110877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d110876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107878 q = 1) (hb : d110877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107878, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107878, d110877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17109 (p : Pattern) (ha : d107888 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
    | true =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107888 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107888, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107888, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17110 (p : Pattern) (ha : d107891 p = 1) (hb : d110886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d110876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d110876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107891 q = 1) (hb : d110886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107891, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107891, d110886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17111 (p : Pattern) (ha : d107898 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
    | true =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107893 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17110 q ha hb
    | true =>
      simp only [d107893, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q hb ha
  have h7 (q : Pattern) (ha : d107894 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107894, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107894, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107895 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107895, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107895, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107896 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107896, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107896, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107897 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107897, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107897, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107898 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107898, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107898, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17112 (p : Pattern) (ha : d107903 p = 1) (hb : d110897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d110896 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107903 q = 1) (hb : d110897 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107903, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107903, d110897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17113 (p : Pattern) (ha : d107912 p = 1) (hb : d110904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d110902 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d110903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107912 q = 1) (hb : d110904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107912, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107912, d110904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17114 (p : Pattern) (ha : d107924 p = 1) (hb : d110909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11156 q = 1) (hb : d107919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11157 q = 1) (hb : d107920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11158 q = 1) (hb : d107921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11159 q = 1) (hb : d107922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107923 q = 1) (hb : d110908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107923, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107923, d110908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107924 q = 1) (hb : d110909 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107924, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107924, d110909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17115 (p : Pattern) (ha : d107930 p = 1) (hb : d110915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d110910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17114 q ha hb
    | true =>
      simp only [d107925, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d110911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d110912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d110913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d110914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107930 q = 1) (hb : d110915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107930, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107930, d110915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17116 (p : Pattern) (ha : d107938 p = 1) (hb : d110871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11102 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d107936 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107937 q = 1) (hb : d110870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107937, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107937, d110870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107938 q = 1) (hb : d110871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107938, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107938, d110871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17117 (p : Pattern) (ha : d107944 p = 1) (hb : d110921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17116 q ha hb
    | true =>
      simp only [d107939, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d110918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d110919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d110920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107944 q = 1) (hb : d110921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107944, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107944, d110921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17118 (p : Pattern) (ha : d107950 p = 1) (hb : d110927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d110898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17112 q ha hb
    | true =>
      simp only [d107906, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15987 q hb ha
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d110899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d110900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d110901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d110905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17113 q ha hb
    | true =>
      simp only [d107916, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15989 q hb ha
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d110906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d110907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d110916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17115 q ha hb
    | true =>
      simp only [d107931, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d110917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d110922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17117 q ha hb
    | true =>
      simp only [d107945, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d110923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d110924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d110925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d110926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107950 q = 1) (hb : d110927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d110927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17119 (p : Pattern) (ha : d107951 p = 1) (hb : d110928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d110875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d110875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d110896 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d110896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107951 q = 1) (hb : d110928 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107951, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107951, d110928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17120 (p : Pattern) (ha : d107957 p = 1) (hb : d110933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d110874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d110874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d110902 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d110902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d110903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d110903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107957 q = 1) (hb : d110933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107957, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107957, d110933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17121 (p : Pattern) (ha : d107962 p = 1) (hb : d110937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d110910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17114 q ha hb
    | true =>
      simp only [d107925, d110910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d110911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d110911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17107 q ha hb
    | true =>
      simp only [d107869, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d110912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d110912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d110913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d110913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d110914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d110914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107962 q = 1) (hb : d110937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107962, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107962, d110937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17122 (p : Pattern) (ha : d107965 p = 1) (hb : d110940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d110872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17116 q ha hb
    | true =>
      simp only [d107939, d110872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d110873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d110873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d110918 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d110918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d110919 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d110919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d110920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d110920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107965 q = 1) (hb : d110940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107965, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107965, d110940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17123 (p : Pattern) (ha : d107971 p = 1) (hb : d110946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d110898 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17112 q ha hb
    | true =>
      simp only [d107906, d110898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15987 q hb ha
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d110899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d110899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d110900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d110900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d110901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d110901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d110905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17113 q ha hb
    | true =>
      simp only [d107916, d110905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15989 q hb ha
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d110906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d110906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d110907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d110907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d110916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17115 q ha hb
    | true =>
      simp only [d107931, d110916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d110917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d110917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d110922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17117 q ha hb
    | true =>
      simp only [d107945, d110922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d110923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d110923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d110924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d110924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d110925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d110925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d110926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d110926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107953 q = 1) (hb : d110929 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107953, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17119 q ha hb
    | true =>
      simp only [d107953, d110929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15996 q hb ha
  have h17 (q : Pattern) (ha : d107954 q = 1) (hb : d110930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107954, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107954, d110930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107955 q = 1) (hb : d110931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107955, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107955, d110931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107956 q = 1) (hb : d110932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107956, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107956, d110932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107959 q = 1) (hb : d110934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107959, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17120 q ha hb
    | true =>
      simp only [d107959, d110934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15998 q hb ha
  have h21 (q : Pattern) (ha : d107960 q = 1) (hb : d110935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107960, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107960, d110935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107961 q = 1) (hb : d110936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107961, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107961, d110936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107963 q = 1) (hb : d110938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17121 q ha hb
    | true =>
      simp only [d107963, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17110 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107964 q = 1) (hb : d110939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107964, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107966 q = 1) (hb : d110941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17122 q ha hb
    | true =>
      simp only [d107966, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107967 q = 1) (hb : d110942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107967, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107968 q = 1) (hb : d110943 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107968, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107969 q = 1) (hb : d110944 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107969, d110944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107970 q = 1) (hb : d110945 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107970, d110945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107971 q = 1) (hb : d110946 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107971, d110946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17124 (p : Pattern) (ha : d107978 p = 1) (hb : d110948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17108 q ha hb
    | true =>
      simp only [d107883, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q hb ha
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d107973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
    | true =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d107974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d107975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d107976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d107977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107978 q = 1) (hb : d110948 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107978, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107978, d110948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17125 (p : Pattern) (ha : d107991 p = 1) (hb : d110955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107963 q = 1) (hb : d110938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17121 q ha hb
    | true =>
      simp only [d107963, d110938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17110 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d110939 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107964, d110939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107966 q = 1) (hb : d110941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17122 q ha hb
    | true =>
      simp only [d107966, d110941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107967 q = 1) (hb : d110942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107967, d110942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107968 q = 1) (hb : d110943 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d110943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107989 q = 1) (hb : d110953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d110953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107990 q = 1) (hb : d110954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d110954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107991 q = 1) (hb : d110955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d110955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17126 (p : Pattern) (ha : d108011 p = 1) (hb : d110962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11264 q = 1) (hb : d107999 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d107999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d11264, d107999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11265 q = 1) (hb : d108000 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d108000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d108000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11266 q = 1) (hb : d108001 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d108001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d108001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11267 q = 1) (hb : d108002 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11268 q = 1) (hb : d108003 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11269 q = 1) (hb : d108004 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11270 q = 1) (hb : d108005 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d108005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11270, d108005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108010 q = 1) (hb : d110961 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108010, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108010, d110961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108011 q = 1) (hb : d110962 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108011, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108011, d110962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17127 (p : Pattern) (ha : d108016 p = 1) (hb : d110966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11267 q = 1) (hb : d108002 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11268 q = 1) (hb : d108003 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11269 q = 1) (hb : d108004 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11271 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11272 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11273 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11274 q = 1) (hb : d108009 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108014 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108015 q = 1) (hb : d110965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108015, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108015, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108016 q = 1) (hb : d110966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108016, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108016, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17128 (p : Pattern) (ha : d108022 p = 1) (hb : d110972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108012 q = 1) (hb : d110963 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108012, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17126 q ha hb
    | true =>
      simp only [d108012, d110963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108013 q = 1) (hb : d110964 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108013, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108013, d110964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108017 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17127 q ha hb
    | true =>
      simp only [d108017, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108018 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108019 q = 1) (hb : d110969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108019, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108019, d110969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108020 q = 1) (hb : d110970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108020, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108020, d110970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108021 q = 1) (hb : d110971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108021, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108021, d110971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108022 q = 1) (hb : d110972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108022, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108022, d110972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17129 (p : Pattern) (ha : d108030 p = 1) (hb : d110976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108017 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17127 q ha hb
    | true =>
      simp only [d108017, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108018 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d108025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15983 q ha hb
    | true =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d108026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108027 q = 1) (hb : d110973 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108027, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108027, d110973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108028 q = 1) (hb : d110974 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108028, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108028, d110974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108029 q = 1) (hb : d110975 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108029, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108029, d110975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108030 q = 1) (hb : d110976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108030, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108030, d110976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17130 (p : Pattern) (ha : d108043 p = 1) (hb : d110966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11267 q = 1) (hb : d108002 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11268 q = 1) (hb : d108003 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11269 q = 1) (hb : d108004 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11271 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11272 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11273 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11274 q = 1) (hb : d108009 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108041 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108042 q = 1) (hb : d110965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108042, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108042, d110965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108043 q = 1) (hb : d110966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108043, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108043, d110966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17131 (p : Pattern) (ha : d108049 p = 1) (hb : d110982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108044 q = 1) (hb : d110967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108044, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17130 q ha hb
    | true =>
      simp only [d108044, d110967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108045 q = 1) (hb : d110968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108045, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108045, d110968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108046 q = 1) (hb : d110979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108046, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108046, d110979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108047 q = 1) (hb : d110980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108047, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108047, d110980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108048 q = 1) (hb : d110981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108048, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108048, d110981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108049 q = 1) (hb : d110982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108049, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108049, d110982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17132 (p : Pattern) (ha : d108055 p = 1) (hb : d110988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108031 q = 1) (hb : d110977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108031, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17128 q ha hb
    | true =>
      simp only [d108031, d110977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17129 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d110978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108037, d110978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108050 q = 1) (hb : d110983 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108050, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17131 q ha hb
    | true =>
      simp only [d108050, d110983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108051 q = 1) (hb : d110984 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108051, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108051, d110984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108052 q = 1) (hb : d110985 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d110985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108053 q = 1) (hb : d110986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d110986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108054 q = 1) (hb : d110987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d110987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108055 q = 1) (hb : d110988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d110988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17133 (p : Pattern) (ha : d108068 p = 1) (hb : d110994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107889 q = 1) (hb : d110884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107889, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107889, d110884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17109 q ha hb
  have h2 (q : Pattern) (ha : d107890 q = 1) (hb : d110885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107890, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107890, d110885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107899 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107899, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17109 q ha hb
    | true =>
      simp only [d107899, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17111 q ha hb
  have h4 (q : Pattern) (ha : d107900 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107900, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107900, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107901 q = 1) (hb : d110895 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107901, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107901, d110895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107972 q = 1) (hb : d110947 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17118 q ha hb
    | true =>
      simp only [d107972, d110947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17123 q ha hb
  have h7 (q : Pattern) (ha : d107985 q = 1) (hb : d110949 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107985, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17124 q ha hb
    | true =>
      simp only [d107985, d110949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15981 q hb ha
  have h8 (q : Pattern) (ha : d107986 q = 1) (hb : d110950 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107986, d110950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107987 q = 1) (hb : d110951 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107987, d110951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107988 q = 1) (hb : d110952 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107988, d110952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107992 q = 1) (hb : d110956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107992, d110956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17125 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d107994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d107994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d107994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15982 q ha hb
  have h13 (q : Pattern) (ha : d107995 q = 1) (hb : d110957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107995, d110957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107996 q = 1) (hb : d110958 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107996, d110958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107997 q = 1) (hb : d110959 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107997, d110959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107998 q = 1) (hb : d110960 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107998, d110960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108056 q = 1) (hb : d110989 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108056, d110989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17132 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d108063 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d108063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d108063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15985 q ha hb
  have h19 (q : Pattern) (ha : d108064 q = 1) (hb : d110990 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108064, d110990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d108065 q = 1) (hb : d110991 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108065, d110991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108066 q = 1) (hb : d110992 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108066, d110992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108067 q = 1) (hb : d110993 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108067, d110993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108068 q = 1) (hb : d110994 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108068, d110994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17134 (p : Pattern) (ha : d108074 p = 1) (hb : d111000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d110995 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d110995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17133 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d110996 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d110996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d110997 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d110997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d110998 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d110998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d110999 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d110999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d111000 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d111000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17135 (p : Pattern) (ha : d108086 p = 1) (hb : d111004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11366 q = 1) (hb : d108077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11367 q = 1) (hb : d108078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11368 q = 1) (hb : d108079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11369 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11370 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11371 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11372 q = 1) (hb : d108083 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108084 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108085 q = 1) (hb : d111003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108085, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108085, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108086 q = 1) (hb : d111004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108086, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108086, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17136 (p : Pattern) (ha : d108096 p = 1) (hb : d111010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d111009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108096 q = 1) (hb : d111010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108096, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108096, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17137 (p : Pattern) (ha : d108106 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
    | true =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108106 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108106, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108106, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17138 (p : Pattern) (ha : d108109 p = 1) (hb : d111019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d111009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108109 q = 1) (hb : d111019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108109, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108109, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17139 (p : Pattern) (ha : d108116 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
    | true =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108111 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17138 q ha hb
    | true =>
      simp only [d108111, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16018 q hb ha
  have h7 (q : Pattern) (ha : d108112 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108112, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108112, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108113 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108113, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108113, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108114 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108114, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108114, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108115 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108115, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108115, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108116 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108116, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108116, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17140 (p : Pattern) (ha : d108121 p = 1) (hb : d111030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d111029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108121 q = 1) (hb : d111030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108121, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108121, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17141 (p : Pattern) (ha : d108130 p = 1) (hb : d111037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d111035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d111036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108130 q = 1) (hb : d111037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108130, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108130, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17142 (p : Pattern) (ha : d108142 p = 1) (hb : d111042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11426 q = 1) (hb : d108137 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d108137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d11426, d108137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11427 q = 1) (hb : d108138 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d108138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d108138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11428 q = 1) (hb : d108139 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d108139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d108139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11366 q = 1) (hb : d108077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11367 q = 1) (hb : d108078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11368 q = 1) (hb : d108079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11429 q = 1) (hb : d108140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d108140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11429, d108140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108083 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108141 q = 1) (hb : d111041 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108141, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108141, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108142 q = 1) (hb : d111042 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108142, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108142, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17143 (p : Pattern) (ha : d108148 p = 1) (hb : d111048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d111043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17142 q ha hb
    | true =>
      simp only [d108143, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d111044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d111045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d111046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d111047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108148 q = 1) (hb : d111048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108148, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108148, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17144 (p : Pattern) (ha : d108156 p = 1) (hb : d111004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11366 q = 1) (hb : d108077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11367 q = 1) (hb : d108078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11368 q = 1) (hb : d108079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11369 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11370 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11371 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11372 q = 1) (hb : d108083 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108154 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108155 q = 1) (hb : d111003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108155, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108155, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108156 q = 1) (hb : d111004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108156, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108156, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17145 (p : Pattern) (ha : d108162 p = 1) (hb : d111054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17144 q ha hb
    | true =>
      simp only [d108157, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d111051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d111052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d111053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108162 q = 1) (hb : d111054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108162, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108162, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17146 (p : Pattern) (ha : d108168 p = 1) (hb : d111060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d111031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17140 q ha hb
    | true =>
      simp only [d108124, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16027 q hb ha
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d111032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d111033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d111034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d111038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17141 q ha hb
    | true =>
      simp only [d108134, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16029 q hb ha
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d111039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d111040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d111049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17143 q ha hb
    | true =>
      simp only [d108149, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d111050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d111055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17145 q ha hb
    | true =>
      simp only [d108163, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d111056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d111057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d111058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d111059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108168 q = 1) (hb : d111060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17147 (p : Pattern) (ha : d108169 p = 1) (hb : d111061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d111029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108169 q = 1) (hb : d111061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108169, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108169, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17148 (p : Pattern) (ha : d108175 p = 1) (hb : d111066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d108091 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16013 q ha hb
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d108092 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d111035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d111036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108175 q = 1) (hb : d111066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108175, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108175, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17149 (p : Pattern) (ha : d108180 p = 1) (hb : d111070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d111043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17142 q ha hb
    | true =>
      simp only [d108143, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d111044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17135 q ha hb
    | true =>
      simp only [d108087, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d111045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d111046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d111047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108180 q = 1) (hb : d111070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108180, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108180, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17150 (p : Pattern) (ha : d108183 p = 1) (hb : d111073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17144 q ha hb
    | true =>
      simp only [d108157, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d111051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d111052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d111053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108183 q = 1) (hb : d111073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108183, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108183, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17151 (p : Pattern) (ha : d108189 p = 1) (hb : d111079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d111031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17140 q ha hb
    | true =>
      simp only [d108124, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16027 q hb ha
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d111032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d111033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d111034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d111038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17141 q ha hb
    | true =>
      simp only [d108134, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16029 q hb ha
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d111039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d111040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d111049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17143 q ha hb
    | true =>
      simp only [d108149, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d111050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d111055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17145 q ha hb
    | true =>
      simp only [d108163, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d111056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d111057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d111058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d111059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108171 q = 1) (hb : d111062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108171, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17147 q ha hb
    | true =>
      simp only [d108171, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16036 q hb ha
  have h17 (q : Pattern) (ha : d108172 q = 1) (hb : d111063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108172, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108172, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108173 q = 1) (hb : d111064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108173, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108173, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108174 q = 1) (hb : d111065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108174, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108174, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108177 q = 1) (hb : d111067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108177, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17148 q ha hb
    | true =>
      simp only [d108177, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16038 q hb ha
  have h21 (q : Pattern) (ha : d108178 q = 1) (hb : d111068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108178, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108178, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108179 q = 1) (hb : d111069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108179, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108179, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108181 q = 1) (hb : d111071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17149 q ha hb
    | true =>
      simp only [d108181, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17138 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108182 q = 1) (hb : d111072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108182, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108184 q = 1) (hb : d111074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17150 q ha hb
    | true =>
      simp only [d108184, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108185 q = 1) (hb : d111075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108185, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108186 q = 1) (hb : d111076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108186, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108187 q = 1) (hb : d111077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108187, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108188 q = 1) (hb : d111078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108188, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108189 q = 1) (hb : d111079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108189, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17152 (p : Pattern) (ha : d108196 p = 1) (hb : d111081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17136 q ha hb
    | true =>
      simp only [d108101, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q hb ha
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d108191 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16015 q ha hb
    | true =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d108192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d108193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d108194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d108195 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108196 q = 1) (hb : d111081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108196, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108196, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17153 (p : Pattern) (ha : d108209 p = 1) (hb : d111088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108181 q = 1) (hb : d111071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17149 q ha hb
    | true =>
      simp only [d108181, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17138 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d111072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108182, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108184 q = 1) (hb : d111074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17150 q ha hb
    | true =>
      simp only [d108184, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108185 q = 1) (hb : d111075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108185, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108186 q = 1) (hb : d111076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108207 q = 1) (hb : d111086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108208 q = 1) (hb : d111087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108209 q = 1) (hb : d111088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17154 (p : Pattern) (ha : d108229 p = 1) (hb : d111095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11534 q = 1) (hb : d108217 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d108217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d11534, d108217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11535 q = 1) (hb : d108218 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d108218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d108218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11536 q = 1) (hb : d108219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d108219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d108219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11537 q = 1) (hb : d108220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11538 q = 1) (hb : d108221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11539 q = 1) (hb : d108222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11540 q = 1) (hb : d108223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d108223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11540, d108223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108227 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108228 q = 1) (hb : d111094 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108228, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108228, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108229 q = 1) (hb : d111095 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108229, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108229, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17155 (p : Pattern) (ha : d108234 p = 1) (hb : d111099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11537 q = 1) (hb : d108220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11538 q = 1) (hb : d108221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11539 q = 1) (hb : d108222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11541 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11542 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11543 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11544 q = 1) (hb : d108227 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108233 q = 1) (hb : d111098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108233, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108233, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108234 q = 1) (hb : d111099 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108234, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108234, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17156 (p : Pattern) (ha : d108240 p = 1) (hb : d111105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108230 q = 1) (hb : d111096 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108230, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17154 q ha hb
    | true =>
      simp only [d108230, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108231 q = 1) (hb : d111097 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108231, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108231, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108235 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17155 q ha hb
    | true =>
      simp only [d108235, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108236 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108237 q = 1) (hb : d111102 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108237, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108237, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108238 q = 1) (hb : d111103 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108238, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108238, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108239 q = 1) (hb : d111104 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108239, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108239, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108240 q = 1) (hb : d111105 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108240, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108240, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17157 (p : Pattern) (ha : d108248 p = 1) (hb : d111109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108235 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17155 q ha hb
    | true =>
      simp only [d108235, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108236 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d108243 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16023 q ha hb
    | true =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d108244 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108245 q = 1) (hb : d111106 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108245, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108245, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108246 q = 1) (hb : d111107 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108246, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108246, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108247 q = 1) (hb : d111108 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108247, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108247, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108248 q = 1) (hb : d111109 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108248, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108248, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17158 (p : Pattern) (ha : d108261 p = 1) (hb : d111099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11537 q = 1) (hb : d108220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11538 q = 1) (hb : d108221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11539 q = 1) (hb : d108222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11541 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11542 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11543 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11544 q = 1) (hb : d108227 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108259 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108260 q = 1) (hb : d111098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108260, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108260, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108261 q = 1) (hb : d111099 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108261, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108261, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17159 (p : Pattern) (ha : d108267 p = 1) (hb : d111115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108262 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108262, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17158 q ha hb
    | true =>
      simp only [d108262, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108263 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108263, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108263, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108264 q = 1) (hb : d111112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108264, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108264, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108265 q = 1) (hb : d111113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108265, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108265, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108266 q = 1) (hb : d111114 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108266, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108266, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108267 q = 1) (hb : d111115 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108267, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108267, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17160 (p : Pattern) (ha : d108273 p = 1) (hb : d111121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108249 q = 1) (hb : d111110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108249, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17156 q ha hb
    | true =>
      simp only [d108249, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17157 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d111111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108255, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108268 q = 1) (hb : d111116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108268, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17159 q ha hb
    | true =>
      simp only [d108268, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108269 q = 1) (hb : d111117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108269, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108269, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108270 q = 1) (hb : d111118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108271 q = 1) (hb : d111119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108272 q = 1) (hb : d111120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108273 q = 1) (hb : d111121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17161 (p : Pattern) (ha : d108286 p = 1) (hb : d111127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108107 q = 1) (hb : d111017 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108107, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108107, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17137 q ha hb
  have h2 (q : Pattern) (ha : d108108 q = 1) (hb : d111018 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108108, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108108, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108117 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108117, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17137 q ha hb
    | true =>
      simp only [d108117, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17139 q ha hb
  have h4 (q : Pattern) (ha : d108118 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108118, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108118, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108119 q = 1) (hb : d111028 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108119, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108119, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108190 q = 1) (hb : d111080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17146 q ha hb
    | true =>
      simp only [d108190, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17151 q ha hb
  have h7 (q : Pattern) (ha : d108203 q = 1) (hb : d111082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108203, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17152 q ha hb
    | true =>
      simp only [d108203, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16021 q hb ha
  have h8 (q : Pattern) (ha : d108204 q = 1) (hb : d111083 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108204, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108205 q = 1) (hb : d111084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108205, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108206 q = 1) (hb : d111085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108206, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108210 q = 1) (hb : d111089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108210, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17153 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d108212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d108212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d108212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16022 q ha hb
  have h13 (q : Pattern) (ha : d108213 q = 1) (hb : d111090 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108213, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d108214 q = 1) (hb : d111091 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108214, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108215 q = 1) (hb : d111092 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108215, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108216 q = 1) (hb : d111093 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108216, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108274 q = 1) (hb : d111122 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108274, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17160 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d108281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d108281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d108281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16025 q ha hb
  have h19 (q : Pattern) (ha : d108282 q = 1) (hb : d111123 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108282, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d108283 q = 1) (hb : d111124 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108283, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108284 q = 1) (hb : d111125 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108284, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108285 q = 1) (hb : d111126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108285, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108286 q = 1) (hb : d111127 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108286, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17162 (p : Pattern) (ha : d108292 p = 1) (hb : d111133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d111128 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17161 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d111129 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d111130 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d111131 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d111132 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d111133 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17163 (p : Pattern) (ha : d108305 p = 1) (hb : d111138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11637 q = 1) (hb : d108296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11638 q = 1) (hb : d108297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11639 q = 1) (hb : d108298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11640 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11641 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11642 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11643 q = 1) (hb : d108302 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108303 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108304 q = 1) (hb : d111137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108304, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108304, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108305 q = 1) (hb : d111138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108305, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108305, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17164 (p : Pattern) (ha : d108315 p = 1) (hb : d111144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d111143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108315 q = 1) (hb : d111144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108315, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108315, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17165 (p : Pattern) (ha : d108325 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
    | true =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108325 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108325, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108325, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17166 (p : Pattern) (ha : d108328 p = 1) (hb : d111153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d111143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108328 q = 1) (hb : d111153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108328, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108328, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17167 (p : Pattern) (ha : d108335 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
    | true =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108330 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17166 q ha hb
    | true =>
      simp only [d108330, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16058 q hb ha
  have h7 (q : Pattern) (ha : d108331 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108331, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108331, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108332 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108332, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108332, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108333 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108333, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108333, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108334 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108334, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108334, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108335 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108335, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108335, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17168 (p : Pattern) (ha : d108340 p = 1) (hb : d111164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108339 q = 1) (hb : d111163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108339, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108339, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108340 q = 1) (hb : d111164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108340, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108340, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17169 (p : Pattern) (ha : d108349 p = 1) (hb : d111171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108347 q = 1) (hb : d111169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108347, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108347, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108348 q = 1) (hb : d111170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108348, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108348, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108349 q = 1) (hb : d111171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108349, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108349, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17170 (p : Pattern) (ha : d108361 p = 1) (hb : d111176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11697 q = 1) (hb : d108356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d108356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d11697, d108356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11698 q = 1) (hb : d108357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d108357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d108357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11699 q = 1) (hb : d108358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d108358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d108358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11637 q = 1) (hb : d108296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11638 q = 1) (hb : d108297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11639 q = 1) (hb : d108298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11700 q = 1) (hb : d108359 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d108359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11700, d108359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108302 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108360 q = 1) (hb : d111175 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108360, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108360, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108361 q = 1) (hb : d111176 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108361, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108361, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17171 (p : Pattern) (ha : d108367 p = 1) (hb : d111182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d111177 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17170 q ha hb
    | true =>
      simp only [d108362, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d111178 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d111179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d111180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d111181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108367 q = 1) (hb : d111182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108367, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108367, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17172 (p : Pattern) (ha : d108375 p = 1) (hb : d111138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11637 q = 1) (hb : d108296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11638 q = 1) (hb : d108297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11639 q = 1) (hb : d108298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11640 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11641 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11642 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11643 q = 1) (hb : d108302 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108373 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108374 q = 1) (hb : d111137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108374, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108374, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108375 q = 1) (hb : d111138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108375, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108375, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17173 (p : Pattern) (ha : d108381 p = 1) (hb : d111188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17172 q ha hb
    | true =>
      simp only [d108376, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d111185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d111186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d111187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108381 q = 1) (hb : d111188 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108381, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108381, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17174 (p : Pattern) (ha : d108387 p = 1) (hb : d111194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d111165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17168 q ha hb
    | true =>
      simp only [d108343, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16067 q hb ha
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d111166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d111167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d111168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d111172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17169 q ha hb
    | true =>
      simp only [d108353, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16069 q hb ha
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d111173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d111174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d111183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17171 q ha hb
    | true =>
      simp only [d108368, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d111184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d111189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17173 q ha hb
    | true =>
      simp only [d108382, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d111190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d111191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d111192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d111193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108387 q = 1) (hb : d111194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17175 (p : Pattern) (ha : d108388 p = 1) (hb : d111195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108339 q = 1) (hb : d111163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108339, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108339, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108388 q = 1) (hb : d111195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108388, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108388, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17176 (p : Pattern) (ha : d108394 p = 1) (hb : d111200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d108310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16053 q ha hb
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d108311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108347 q = 1) (hb : d111169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108347, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108347, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108348 q = 1) (hb : d111170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108348, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108348, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108394 q = 1) (hb : d111200 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108394, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108394, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17177 (p : Pattern) (ha : d108399 p = 1) (hb : d111204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d111177 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17170 q ha hb
    | true =>
      simp only [d108362, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d111178 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17163 q ha hb
    | true =>
      simp only [d108306, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d111179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d111180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d111181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108399 q = 1) (hb : d111204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108399, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108399, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17178 (p : Pattern) (ha : d108402 p = 1) (hb : d111207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17172 q ha hb
    | true =>
      simp only [d108376, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d111185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d111186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d111187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108402 q = 1) (hb : d111207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108402, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108402, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17179 (p : Pattern) (ha : d108408 p = 1) (hb : d111213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d111165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17168 q ha hb
    | true =>
      simp only [d108343, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16067 q hb ha
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d111166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d111167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d111168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d111172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17169 q ha hb
    | true =>
      simp only [d108353, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16069 q hb ha
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d111173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d111174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d111183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17171 q ha hb
    | true =>
      simp only [d108368, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d111184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d111189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17173 q ha hb
    | true =>
      simp only [d108382, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d111190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d111191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d111192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d111193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108390 q = 1) (hb : d111196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108390, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17175 q ha hb
    | true =>
      simp only [d108390, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16076 q hb ha
  have h17 (q : Pattern) (ha : d108391 q = 1) (hb : d111197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108391, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108391, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108392 q = 1) (hb : d111198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108392, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108392, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108393 q = 1) (hb : d111199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108393, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108393, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108396 q = 1) (hb : d111201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108396, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17176 q ha hb
    | true =>
      simp only [d108396, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16078 q hb ha
  have h21 (q : Pattern) (ha : d108397 q = 1) (hb : d111202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108397, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108397, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108398 q = 1) (hb : d111203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108398, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108398, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108400 q = 1) (hb : d111205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17177 q ha hb
    | true =>
      simp only [d108400, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17166 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108401 q = 1) (hb : d111206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108401, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108403 q = 1) (hb : d111208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17178 q ha hb
    | true =>
      simp only [d108403, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108404 q = 1) (hb : d111209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108404, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108405 q = 1) (hb : d111210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108405, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108406 q = 1) (hb : d111211 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108406, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108407 q = 1) (hb : d111212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108407, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108408 q = 1) (hb : d111213 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108408, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17180 (p : Pattern) (ha : d108415 p = 1) (hb : d111215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17164 q ha hb
    | true =>
      simp only [d108320, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q hb ha
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d108410 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16055 q ha hb
    | true =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d108411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d108412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d108413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d108414 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108415 q = 1) (hb : d111215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108415, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108415, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17181 (p : Pattern) (ha : d108428 p = 1) (hb : d111222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108400 q = 1) (hb : d111205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17177 q ha hb
    | true =>
      simp only [d108400, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17166 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d111206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108401, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108403 q = 1) (hb : d111208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17178 q ha hb
    | true =>
      simp only [d108403, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108404 q = 1) (hb : d111209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108404, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108405 q = 1) (hb : d111210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108426 q = 1) (hb : d111220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108427 q = 1) (hb : d111221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108428 q = 1) (hb : d111222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17182 (p : Pattern) (ha : d108448 p = 1) (hb : d111229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11805 q = 1) (hb : d108436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d108436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d11805, d108436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11806 q = 1) (hb : d108437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d108437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11806, d108437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11807 q = 1) (hb : d108438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d108438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11807, d108438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11808 q = 1) (hb : d108439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11809 q = 1) (hb : d108440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11810 q = 1) (hb : d108441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11811 q = 1) (hb : d108442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d108442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11811, d108442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108446 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108447 q = 1) (hb : d111228 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108447, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108447, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108448 q = 1) (hb : d111229 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108448, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108448, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17183 (p : Pattern) (ha : d108453 p = 1) (hb : d111233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11808 q = 1) (hb : d108439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11809 q = 1) (hb : d108440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11810 q = 1) (hb : d108441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11812 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11813 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11814 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11815 q = 1) (hb : d108446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108452 q = 1) (hb : d111232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108452, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108452, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108453 q = 1) (hb : d111233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108453, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108453, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17184 (p : Pattern) (ha : d108459 p = 1) (hb : d111239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108449 q = 1) (hb : d111230 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108449, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17182 q ha hb
    | true =>
      simp only [d108449, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108450 q = 1) (hb : d111231 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108450, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108450, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108454 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17183 q ha hb
    | true =>
      simp only [d108454, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108455 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108456 q = 1) (hb : d111236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108456, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108456, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108457 q = 1) (hb : d111237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108457, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108457, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108458 q = 1) (hb : d111238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108458, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108458, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108459 q = 1) (hb : d111239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108459, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108459, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17185 (p : Pattern) (ha : d108467 p = 1) (hb : d111243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108454 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17183 q ha hb
    | true =>
      simp only [d108454, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108455 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11831 q = 1) (hb : d108462 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16063 q ha hb
    | true =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11832 q = 1) (hb : d108463 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108464 q = 1) (hb : d111240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108464, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108464, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108465 q = 1) (hb : d111241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108465, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108465, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108466 q = 1) (hb : d111242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108466, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108466, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108467 q = 1) (hb : d111243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108467, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108467, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17186 (p : Pattern) (ha : d108480 p = 1) (hb : d111233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11808 q = 1) (hb : d108439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11809 q = 1) (hb : d108440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11810 q = 1) (hb : d108441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11812 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11813 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11814 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11815 q = 1) (hb : d108446 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108478 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108479 q = 1) (hb : d111232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108479, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108479, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108480 q = 1) (hb : d111233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108480, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108480, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17187 (p : Pattern) (ha : d108486 p = 1) (hb : d111249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108481 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108481, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17186 q ha hb
    | true =>
      simp only [d108481, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108482 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108482, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108482, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108483 q = 1) (hb : d111246 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108483, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108483, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108484 q = 1) (hb : d111247 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108484, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108484, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108485 q = 1) (hb : d111248 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108485, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108485, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108486 q = 1) (hb : d111249 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108486, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108486, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17188 (p : Pattern) (ha : d108492 p = 1) (hb : d111255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108468 q = 1) (hb : d111244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108468, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17184 q ha hb
    | true =>
      simp only [d108468, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17185 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d111245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108474, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108487 q = 1) (hb : d111250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108487, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17187 q ha hb
    | true =>
      simp only [d108487, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108488 q = 1) (hb : d111251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108488, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108488, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108489 q = 1) (hb : d111252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108490 q = 1) (hb : d111253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108491 q = 1) (hb : d111254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108492 q = 1) (hb : d111255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17189 (p : Pattern) (ha : d108505 p = 1) (hb : d111261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108326 q = 1) (hb : d111151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108326, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108326, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17165 q ha hb
  have h2 (q : Pattern) (ha : d108327 q = 1) (hb : d111152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108327, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108327, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108336 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108336, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17165 q ha hb
    | true =>
      simp only [d108336, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17167 q ha hb
  have h4 (q : Pattern) (ha : d108337 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108337, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108337, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108338 q = 1) (hb : d111162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108338, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108338, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108409 q = 1) (hb : d111214 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17174 q ha hb
    | true =>
      simp only [d108409, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17179 q ha hb
  have h7 (q : Pattern) (ha : d108422 q = 1) (hb : d111216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108422, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17180 q ha hb
    | true =>
      simp only [d108422, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16061 q hb ha
  have h8 (q : Pattern) (ha : d108423 q = 1) (hb : d111217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108423, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108424 q = 1) (hb : d111218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108424, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108425 q = 1) (hb : d111219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108425, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108429 q = 1) (hb : d111223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108429, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17181 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d108431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d108431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, d108431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16062 q ha hb
  have h13 (q : Pattern) (ha : d108432 q = 1) (hb : d111224 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108432, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d108433 q = 1) (hb : d111225 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108433, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108434 q = 1) (hb : d111226 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108434, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108435 q = 1) (hb : d111227 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108435, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108493 q = 1) (hb : d111256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108493, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17188 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d108500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d108500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, d108500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16065 q ha hb
  have h19 (q : Pattern) (ha : d108501 q = 1) (hb : d111257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108501, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d108502 q = 1) (hb : d111258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108502, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108503 q = 1) (hb : d111259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108503, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108504 q = 1) (hb : d111260 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108504, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108505 q = 1) (hb : d111261 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108505, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17190 (p : Pattern) (ha : d108511 p = 1) (hb : d111267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d111262 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17189 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d111263 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d111264 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d111265 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d111266 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d111267 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17191 (p : Pattern) (ha : d108525 p = 1) (hb : d111273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11909 q = 1) (hb : d108516 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11910 q = 1) (hb : d108517 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11911 q = 1) (hb : d108518 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11912 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11913 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11914 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11915 q = 1) (hb : d108522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108523 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108524 q = 1) (hb : d111272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108524, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108524, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108525 q = 1) (hb : d111273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108525, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108525, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17192 (p : Pattern) (ha : d108535 p = 1) (hb : d111279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d111278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108535 q = 1) (hb : d111279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108535, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108535, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17193 (p : Pattern) (ha : d108545 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
    | true =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108545 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108545, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108545, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17194 (p : Pattern) (ha : d108548 p = 1) (hb : d111288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d111278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108548 q = 1) (hb : d111288 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108548, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108548, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17195 (p : Pattern) (ha : d108555 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
    | true =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108550 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17194 q ha hb
    | true =>
      simp only [d108550, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16098 q hb ha
  have h7 (q : Pattern) (ha : d108551 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108551, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108551, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108552 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108552, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108552, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108553 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108553, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108553, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108554 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108554, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108554, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108555 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108555, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108555, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro17196 (p : Pattern) (ha : d108560 p = 1) (hb : d111299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d111298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108560 q = 1) (hb : d111299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108560, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108560, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17197 (p : Pattern) (ha : d108569 p = 1) (hb : d111306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d111304 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d111305 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108569 q = 1) (hb : d111306 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108569, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108569, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17198 (p : Pattern) (ha : d108581 p = 1) (hb : d111311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11969 q = 1) (hb : d108576 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d108576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d11969, d108576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11970 q = 1) (hb : d108577 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d108577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11970, d108577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11971 q = 1) (hb : d108578 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d108578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11971, d108578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11909 q = 1) (hb : d108516 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11910 q = 1) (hb : d108517 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11911 q = 1) (hb : d108518 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11972 q = 1) (hb : d108579 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d108579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11972, d108579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108522 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108580 q = 1) (hb : d111310 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108580, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108580, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108581 q = 1) (hb : d111311 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108581, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108581, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17199 (p : Pattern) (ha : d108587 p = 1) (hb : d111317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d111312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17198 q ha hb
    | true =>
      simp only [d108582, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d111313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d111314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d111315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d111316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108587 q = 1) (hb : d111317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108587, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108587, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro17200 (p : Pattern) (ha : d108595 p = 1) (hb : d111273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11909 q = 1) (hb : d108516 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11910 q = 1) (hb : d108517 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11911 q = 1) (hb : d108518 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11912 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11913 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11914 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11915 q = 1) (hb : d108522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108593 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108594 q = 1) (hb : d111272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108594, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108594, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108595 q = 1) (hb : d111273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108595, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108595, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17201 (p : Pattern) (ha : d108601 p = 1) (hb : d111323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17200 q ha hb
    | true =>
      simp only [d108596, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d111320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d111321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d111322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108601 q = 1) (hb : d111323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108601, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108601, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17202 (p : Pattern) (ha : d108607 p = 1) (hb : d111329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d111300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17196 q ha hb
    | true =>
      simp only [d108563, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16107 q hb ha
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d111301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d111302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d111303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d111307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17197 q ha hb
    | true =>
      simp only [d108573, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16109 q hb ha
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d111308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d111309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d111318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17199 q ha hb
    | true =>
      simp only [d108588, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d111319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d111324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17201 q ha hb
    | true =>
      simp only [d108602, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d111325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d111326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d111327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d111328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108607 q = 1) (hb : d111329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro17203 (p : Pattern) (ha : d108608 p = 1) (hb : d111330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d111298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108608 q = 1) (hb : d111330 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108608, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108608, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17204 (p : Pattern) (ha : d108614 p = 1) (hb : d111335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d108530 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16093 q ha hb
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d108531 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d111304 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d111305 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108614 q = 1) (hb : d111335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108614, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108614, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17205 (p : Pattern) (ha : d108619 p = 1) (hb : d111339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d111312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17198 q ha hb
    | true =>
      simp only [d108582, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d111313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17191 q ha hb
    | true =>
      simp only [d108526, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d111314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d111315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d111316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108619 q = 1) (hb : d111339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108619, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108619, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17206 (p : Pattern) (ha : d108622 p = 1) (hb : d111342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17200 q ha hb
    | true =>
      simp only [d108596, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d111320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d111321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d111322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108622 q = 1) (hb : d111342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108622, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108622, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17207 (p : Pattern) (ha : d108628 p = 1) (hb : d111348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d111300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17196 q ha hb
    | true =>
      simp only [d108563, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16107 q hb ha
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d111301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d111302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d111303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d111307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17197 q ha hb
    | true =>
      simp only [d108573, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16109 q hb ha
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d111308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d111309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d111318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17199 q ha hb
    | true =>
      simp only [d108588, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d111319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d111324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17201 q ha hb
    | true =>
      simp only [d108602, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d111325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d111326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d111327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d111328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108610 q = 1) (hb : d111331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108610, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17203 q ha hb
    | true =>
      simp only [d108610, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16116 q hb ha
  have h17 (q : Pattern) (ha : d108611 q = 1) (hb : d111332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108611, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108611, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108612 q = 1) (hb : d111333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108612, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108612, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108613 q = 1) (hb : d111334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108613, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108613, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108616 q = 1) (hb : d111336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108616, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17204 q ha hb
    | true =>
      simp only [d108616, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16118 q hb ha
  have h21 (q : Pattern) (ha : d108617 q = 1) (hb : d111337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108617, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108617, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108618 q = 1) (hb : d111338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108618, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108618, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108620 q = 1) (hb : d111340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17205 q ha hb
    | true =>
      simp only [d108620, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17194 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108621 q = 1) (hb : d111341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108621, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108623 q = 1) (hb : d111343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17206 q ha hb
    | true =>
      simp only [d108623, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108624 q = 1) (hb : d111344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108624, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108625 q = 1) (hb : d111345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108625, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108626 q = 1) (hb : d111346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108626, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108627 q = 1) (hb : d111347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108627, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108628 q = 1) (hb : d111348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108628, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro17208 (p : Pattern) (ha : d108635 p = 1) (hb : d111350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17192 q ha hb
    | true =>
      simp only [d108540, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q hb ha
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d108630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16095 q ha hb
    | true =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d108631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d108632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d108633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d108634 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108635 q = 1) (hb : d111350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108635, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108635, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro17209 (p : Pattern) (ha : d108648 p = 1) (hb : d111357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108620 q = 1) (hb : d111340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17205 q ha hb
    | true =>
      simp only [d108620, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17194 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d111341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108621, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108623 q = 1) (hb : d111343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17206 q ha hb
    | true =>
      simp only [d108623, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108624 q = 1) (hb : d111344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108624, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108625 q = 1) (hb : d111345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108646 q = 1) (hb : d111355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108647 q = 1) (hb : d111356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108648 q = 1) (hb : d111357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17210 (p : Pattern) (ha : d108668 p = 1) (hb : d111364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12077 q = 1) (hb : d108656 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d108656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d12077, d108656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12078 q = 1) (hb : d108657 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d108657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12078, d108657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12079 q = 1) (hb : d108658 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d108658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12079, d108658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12080 q = 1) (hb : d108659 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12081 q = 1) (hb : d108660 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12082 q = 1) (hb : d108661 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12083 q = 1) (hb : d108662 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d108662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12083, d108662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108666 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108667 q = 1) (hb : d111363 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108667, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108667, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108668 q = 1) (hb : d111364 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108668, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108668, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17211 (p : Pattern) (ha : d108673 p = 1) (hb : d111368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12080 q = 1) (hb : d108659 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12081 q = 1) (hb : d108660 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12082 q = 1) (hb : d108661 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12084 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12085 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12086 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12087 q = 1) (hb : d108666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108671 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108672 q = 1) (hb : d111367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108672, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108672, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108673 q = 1) (hb : d111368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108673, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108673, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17212 (p : Pattern) (ha : d108679 p = 1) (hb : d111374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108669 q = 1) (hb : d111365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108669, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17210 q ha hb
    | true =>
      simp only [d108669, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108670 q = 1) (hb : d111366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108670, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108670, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108674 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17211 q ha hb
    | true =>
      simp only [d108674, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108675 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108676 q = 1) (hb : d111371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108676, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108676, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108677 q = 1) (hb : d111372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108677, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108677, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108678 q = 1) (hb : d111373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108678, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108678, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108679 q = 1) (hb : d111374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108679, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108679, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17213 (p : Pattern) (ha : d108687 p = 1) (hb : d111378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108674 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17211 q ha hb
    | true =>
      simp only [d108674, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108675 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12103 q = 1) (hb : d108682 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16103 q ha hb
    | true =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12104 q = 1) (hb : d108683 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108684 q = 1) (hb : d111375 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108684, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108684, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d108685 q = 1) (hb : d111376 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108685, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108685, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108686 q = 1) (hb : d111377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108686, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108686, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108687 q = 1) (hb : d111378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108687, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108687, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro17214 (p : Pattern) (ha : d108700 p = 1) (hb : d111368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12080 q = 1) (hb : d108659 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12081 q = 1) (hb : d108660 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12082 q = 1) (hb : d108661 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12084 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12085 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12086 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12087 q = 1) (hb : d108666 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d108698 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108699 q = 1) (hb : d111367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108699, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108699, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108700 q = 1) (hb : d111368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108700, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108700, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro17215 (p : Pattern) (ha : d108706 p = 1) (hb : d111384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108701 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108701, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17214 q ha hb
    | true =>
      simp only [d108701, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108702 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108702, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108702, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108703 q = 1) (hb : d111381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108703, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108703, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108704 q = 1) (hb : d111382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108704, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108704, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108705 q = 1) (hb : d111383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108705, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108705, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108706 q = 1) (hb : d111384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108706, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108706, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17216 (p : Pattern) (ha : d108712 p = 1) (hb : d111390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108688 q = 1) (hb : d111379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108688, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17212 q ha hb
    | true =>
      simp only [d108688, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17213 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d111380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108694, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108707 q = 1) (hb : d111385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108707, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17215 q ha hb
    | true =>
      simp only [d108707, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108708 q = 1) (hb : d111386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108708, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108708, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108709 q = 1) (hb : d111387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108710 q = 1) (hb : d111388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108711 q = 1) (hb : d111389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108712 q = 1) (hb : d111390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro17217 (p : Pattern) (ha : d108725 p = 1) (hb : d111396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108546 q = 1) (hb : d111286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108546, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108546, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17193 q ha hb
  have h2 (q : Pattern) (ha : d108547 q = 1) (hb : d111287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108547, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108547, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108556 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108556, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17193 q ha hb
    | true =>
      simp only [d108556, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17195 q ha hb
  have h4 (q : Pattern) (ha : d108557 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108557, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108557, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108558 q = 1) (hb : d111297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108558, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108558, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108629 q = 1) (hb : d111349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17202 q ha hb
    | true =>
      simp only [d108629, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17207 q ha hb
  have h7 (q : Pattern) (ha : d108642 q = 1) (hb : d111351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108642, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17208 q ha hb
    | true =>
      simp only [d108642, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16101 q hb ha
  have h8 (q : Pattern) (ha : d108643 q = 1) (hb : d111352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108643, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108644 q = 1) (hb : d111353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108644, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108645 q = 1) (hb : d111354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108645, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108649 q = 1) (hb : d111358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108649, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17209 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d108651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d108651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, d108651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16102 q ha hb
  have h13 (q : Pattern) (ha : d108652 q = 1) (hb : d111359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108652, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d108653 q = 1) (hb : d111360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108653, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108654 q = 1) (hb : d111361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108654, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108655 q = 1) (hb : d111362 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108655, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108713 q = 1) (hb : d111391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108713, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17216 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d108720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d108720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, d108720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16105 q ha hb
  have h19 (q : Pattern) (ha : d108721 q = 1) (hb : d111392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108721, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d108722 q = 1) (hb : d111393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108722, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108723 q = 1) (hb : d111394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108723, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108724 q = 1) (hb : d111395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108724, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108725 q = 1) (hb : d111396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108725, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro17218 (p : Pattern) (ha : d108731 p = 1) (hb : d111402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d111397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17217 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d111398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d111399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d111400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d111401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d111402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17219 (p : Pattern) (ha : d108737 p = 1) (hb : d111408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d110869 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17080 q ha hb
    | true =>
      simp only [d107858, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17106 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d111001 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17134 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d111002 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d111134 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17162 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d111135 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d111136 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d111268 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17190 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d111269 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d111270 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d111271 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d111403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17218 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d111404 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d111405 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d111406 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d111407 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d111408 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro17220 (p : Pattern) (ha : d108743 p = 1) (hb : d111414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d111409 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17219 q ha hb
    | true =>
      simp only [d108738, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d111410 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d111411 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d111412 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d111413 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d111414 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17221 (p : Pattern) (ha : d108749 p = 1) (hb : d111420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d111415 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17220 q ha hb
    | true =>
      simp only [d108744, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d111416 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d111417 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d111418 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d111419 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d111420 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17222 (p : Pattern) (ha : d108755 p = 1) (hb : d111426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d111421 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17221 q ha hb
    | true =>
      simp only [d108750, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d111422 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d111423 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d111424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d111425 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d111426 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17223 (p : Pattern) (ha : d108761 p = 1) (hb : d111432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d111427 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17222 q ha hb
    | true =>
      simp only [d108756, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d111428 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d111429 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d111430 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d111431 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d111432 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17224 (p : Pattern) (ha : d108767 p = 1) (hb : d111438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d111433 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17223 q ha hb
    | true =>
      simp only [d108762, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d111434 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d111435 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d111436 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d111437 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d111438 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17225 (p : Pattern) (ha : d108773 p = 1) (hb : d111444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d111439 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17224 q ha hb
    | true =>
      simp only [d108768, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d111440 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d111441 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d111442 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d111443 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d111444 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17226 (p : Pattern) (ha : d108779 p = 1) (hb : d111450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d111445 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17225 q ha hb
    | true =>
      simp only [d108774, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d111446 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d111447 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d111448 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d111449 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d111450 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro17227 (p : Pattern) (ha : d99199 p = 1) (hb : d107483 p = 1) : d111453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16826 q ha hb
    | true =>
      simp only [d7255, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d107483 q = 1) : d110641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7306 q = 1) (hb : d107483 q = 1) : d110642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7307 q = 1) (hb : d107483 q = 1) : d110643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7308 q = 1) (hb : d107483 q = 1) : d110644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d99199 q = 1) (hb : d107483 q = 1) : d111453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99199, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99199, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17228 (p : Pattern) (ha : d99209 p = 1) (hb : d107483 p = 1) : d111463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d107483 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d107483 q = 1) : d110617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16830 q ha hb
    | true =>
      simp only [d7281, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99205 q = 1) (hb : d107483 q = 1) : d111459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99205, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99205, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99206 q = 1) (hb : d107483 q = 1) : d111460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99206, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99206, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d99207 q = 1) (hb : d107483 q = 1) : d111461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99207, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99207, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99208 q = 1) (hb : d107483 q = 1) : d111462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99208, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99208, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d99209 q = 1) (hb : d107483 q = 1) : d111463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99209, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99209, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17229 (p : Pattern) (ha : d99215 p = 1) (hb : d107483 p = 1) : d111469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d107483 q = 1) : d110646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16833 q ha hb
    | true =>
      simp only [d7310, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16834 q ha hb
  have h2 (q : Pattern) (ha : d7311 q = 1) (hb : d107483 q = 1) : d110647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99197 q = 1) (hb : d107483 q = 1) : d111451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99197, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99197, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99198 q = 1) (hb : d107483 q = 1) : d111452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99198, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99198, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99200 q = 1) (hb : d107483 q = 1) : d111454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99200, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99200, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17227 q ha hb
  have h6 (q : Pattern) (ha : d99201 q = 1) (hb : d107483 q = 1) : d111455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99201, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99201, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99202 q = 1) (hb : d107483 q = 1) : d111456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99202, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99202, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99203 q = 1) (hb : d107483 q = 1) : d111457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99203, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99203, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99204 q = 1) (hb : d107483 q = 1) : d111458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99204, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99204, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99210 q = 1) (hb : d107483 q = 1) : d111464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99210, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99210, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17228 q ha hb
  have h11 (q : Pattern) (ha : d99211 q = 1) (hb : d107483 q = 1) : d111465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99211, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99211, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99212 q = 1) (hb : d107483 q = 1) : d111466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99212, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99212, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99213 q = 1) (hb : d107483 q = 1) : d111467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99213, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99213, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99214 q = 1) (hb : d107483 q = 1) : d111468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99214, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99214, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99215 q = 1) (hb : d107483 q = 1) : d111469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99215, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99215, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17230 (p : Pattern) (ha : d99221 p = 1) (hb : d107483 p = 1) : d111475 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d107483 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d99216 q = 1) (hb : d107483 q = 1) : d111470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99216, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99216, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17229 q ha hb
  have h3 (q : Pattern) (ha : d99217 q = 1) (hb : d107483 q = 1) : d111471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99217, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99217, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99218 q = 1) (hb : d107483 q = 1) : d111472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99218, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99218, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99219 q = 1) (hb : d107483 q = 1) : d111473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99219, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99219, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99220 q = 1) (hb : d107483 q = 1) : d111474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99220, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99220, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d99221 q = 1) (hb : d107483 q = 1) : d111475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99221, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99221, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro17231 (p : Pattern) (ha : d99224 p = 1) (hb : d107483 p = 1) : d111478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7443 q = 1) (hb : d107483 q = 1) : d110759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16864 q ha hb
    | true =>
      simp only [d7443, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16856 q ha hb
  have h2 (q : Pattern) (ha : d7444 q = 1) (hb : d107483 q = 1) : d110760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7445 q = 1) (hb : d107483 q = 1) : d110761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7445, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7446 q = 1) (hb : d107483 q = 1) : d110762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7447 q = 1) (hb : d107483 q = 1) : d110763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99224 q = 1) (hb : d107483 q = 1) : d111478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99224, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99224, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17232 (p : Pattern) (ha : d99235 p = 1) (hb : d107483 p = 1) : d111489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99230 q = 1) (hb : d107483 q = 1) : d111484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99230, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16885 q ha hb
    | true =>
      simp only [d99230, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16860 q ha hb
  have h2 (q : Pattern) (ha : d99231 q = 1) (hb : d107483 q = 1) : d111485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99231, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99231, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99232 q = 1) (hb : d107483 q = 1) : d111486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99232, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99232, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99233 q = 1) (hb : d107483 q = 1) : d111487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99233, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99233, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99234 q = 1) (hb : d107483 q = 1) : d111488 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99234, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99234, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99235 q = 1) (hb : d107483 q = 1) : d111489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99235, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99235, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17233 (p : Pattern) (ha : d99241 p = 1) (hb : d107483 p = 1) : d111495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d107483 q = 1) : d110765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16863 q ha hb
    | true =>
      simp only [d7449, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16865 q ha hb
  have h2 (q : Pattern) (ha : d7450 q = 1) (hb : d107483 q = 1) : d110766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99222 q = 1) (hb : d107483 q = 1) : d111476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99222, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99222, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99223 q = 1) (hb : d107483 q = 1) : d111477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99223, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99223, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99225 q = 1) (hb : d107483 q = 1) : d111479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99225, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99225, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17231 q ha hb
  have h6 (q : Pattern) (ha : d99226 q = 1) (hb : d107483 q = 1) : d111480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99226, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99226, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99227 q = 1) (hb : d107483 q = 1) : d111481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99227, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99227, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99228 q = 1) (hb : d107483 q = 1) : d111482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99228, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99228, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99229 q = 1) (hb : d107483 q = 1) : d111483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99229, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99229, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99236 q = 1) (hb : d107483 q = 1) : d111490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99236, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99236, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17232 q ha hb
  have h11 (q : Pattern) (ha : d99237 q = 1) (hb : d107483 q = 1) : d111491 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99237, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99237, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99238 q = 1) (hb : d107483 q = 1) : d111492 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99238, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99238, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99239 q = 1) (hb : d107483 q = 1) : d111493 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99239, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99239, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99240 q = 1) (hb : d107483 q = 1) : d111494 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99240, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99240, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99241 q = 1) (hb : d107483 q = 1) : d111495 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99241, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99241, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17234 (p : Pattern) (ha : d99247 p = 1) (hb : d107483 p = 1) : d111501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99242 q = 1) (hb : d107483 q = 1) : d111496 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99242, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99242, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17233 q ha hb
  have h2 (q : Pattern) (ha : d99243 q = 1) (hb : d107483 q = 1) : d111497 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99243, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99243, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99244 q = 1) (hb : d107483 q = 1) : d111498 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99244, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99244, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99245 q = 1) (hb : d107483 q = 1) : d111499 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99245, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99245, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99246 q = 1) (hb : d107483 q = 1) : d111500 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99246, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99246, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99247 q = 1) (hb : d107483 q = 1) : d111501 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99247, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99247, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17235 (p : Pattern) (ha : d99251 p = 1) (hb : d107483 p = 1) : d111505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7591 q = 1) (hb : d107483 q = 1) : d110887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16901 q ha hb
    | true =>
      simp only [d7591, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16892 q ha hb
  have h2 (q : Pattern) (ha : d7592 q = 1) (hb : d107483 q = 1) : d110888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7593 q = 1) (hb : d107483 q = 1) : d110889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7593, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7594 q = 1) (hb : d107483 q = 1) : d110890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7595 q = 1) (hb : d107483 q = 1) : d110891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99251 q = 1) (hb : d107483 q = 1) : d111505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99251, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99251, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17236 (p : Pattern) (ha : d99262 p = 1) (hb : d107483 p = 1) : d111516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99257 q = 1) (hb : d107483 q = 1) : d111511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99257, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16923 q ha hb
    | true =>
      simp only [d99257, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16896 q ha hb
  have h2 (q : Pattern) (ha : d99258 q = 1) (hb : d107483 q = 1) : d111512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99258, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99258, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99259 q = 1) (hb : d107483 q = 1) : d111513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99259, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99259, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99260 q = 1) (hb : d107483 q = 1) : d111514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99260, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99260, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99261 q = 1) (hb : d107483 q = 1) : d111515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99261, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99261, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99262 q = 1) (hb : d107483 q = 1) : d111516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99262, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99262, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17237 (p : Pattern) (ha : d99268 p = 1) (hb : d107483 p = 1) : d111522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d107483 q = 1) : d110893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16900 q ha hb
    | true =>
      simp only [d7597, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16902 q ha hb
  have h2 (q : Pattern) (ha : d7598 q = 1) (hb : d107483 q = 1) : d110894 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99249 q = 1) (hb : d107483 q = 1) : d111503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99249, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99249, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99250 q = 1) (hb : d107483 q = 1) : d111504 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99250, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99250, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99252 q = 1) (hb : d107483 q = 1) : d111506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99252, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99252, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17235 q ha hb
  have h6 (q : Pattern) (ha : d99253 q = 1) (hb : d107483 q = 1) : d111507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99253, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99253, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99254 q = 1) (hb : d107483 q = 1) : d111508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99254, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99254, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99255 q = 1) (hb : d107483 q = 1) : d111509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99255, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99255, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99256 q = 1) (hb : d107483 q = 1) : d111510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99256, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99256, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99263 q = 1) (hb : d107483 q = 1) : d111517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99263, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99263, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17236 q ha hb
  have h11 (q : Pattern) (ha : d99264 q = 1) (hb : d107483 q = 1) : d111518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99264, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99264, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99265 q = 1) (hb : d107483 q = 1) : d111519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99265, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99265, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99266 q = 1) (hb : d107483 q = 1) : d111520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99266, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99266, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99267 q = 1) (hb : d107483 q = 1) : d111521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99267, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99267, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99268 q = 1) (hb : d107483 q = 1) : d111522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99268, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99268, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17238 (p : Pattern) (ha : d99274 p = 1) (hb : d107483 p = 1) : d111528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99269 q = 1) (hb : d107483 q = 1) : d111523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99269, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99269, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17237 q ha hb
  have h2 (q : Pattern) (ha : d99270 q = 1) (hb : d107483 q = 1) : d111524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99270, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99270, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99271 q = 1) (hb : d107483 q = 1) : d111525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99271, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99271, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99272 q = 1) (hb : d107483 q = 1) : d111526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99272, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99272, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99273 q = 1) (hb : d107483 q = 1) : d111527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99273, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99273, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99274 q = 1) (hb : d107483 q = 1) : d111528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99274, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99274, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17239 (p : Pattern) (ha : d99279 p = 1) (hb : d107483 p = 1) : d111533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7744 q = 1) (hb : d107483 q = 1) : d111020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16939 q ha hb
    | true =>
      simp only [d7744, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16930 q ha hb
  have h2 (q : Pattern) (ha : d7745 q = 1) (hb : d107483 q = 1) : d111021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7746 q = 1) (hb : d107483 q = 1) : d111022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7746, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7747 q = 1) (hb : d107483 q = 1) : d111023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7748 q = 1) (hb : d107483 q = 1) : d111024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99279 q = 1) (hb : d107483 q = 1) : d111533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99279, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99279, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17240 (p : Pattern) (ha : d99290 p = 1) (hb : d107483 p = 1) : d111544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99285 q = 1) (hb : d107483 q = 1) : d111539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99285, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16961 q ha hb
    | true =>
      simp only [d99285, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16934 q ha hb
  have h2 (q : Pattern) (ha : d99286 q = 1) (hb : d107483 q = 1) : d111540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99286, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99286, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99287 q = 1) (hb : d107483 q = 1) : d111541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99287, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99287, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99288 q = 1) (hb : d107483 q = 1) : d111542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99288, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99288, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99289 q = 1) (hb : d107483 q = 1) : d111543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99289, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99289, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99290 q = 1) (hb : d107483 q = 1) : d111544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99290, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99290, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17241 (p : Pattern) (ha : d99296 p = 1) (hb : d107483 p = 1) : d111550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d107483 q = 1) : d111026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16938 q ha hb
    | true =>
      simp only [d7750, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16940 q ha hb
  have h2 (q : Pattern) (ha : d7751 q = 1) (hb : d107483 q = 1) : d111027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99277 q = 1) (hb : d107483 q = 1) : d111531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99277, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99277, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99278 q = 1) (hb : d107483 q = 1) : d111532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99278, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99278, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99280 q = 1) (hb : d107483 q = 1) : d111534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99280, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99280, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17239 q ha hb
  have h6 (q : Pattern) (ha : d99281 q = 1) (hb : d107483 q = 1) : d111535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99281, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99281, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99282 q = 1) (hb : d107483 q = 1) : d111536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99282, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99282, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99283 q = 1) (hb : d107483 q = 1) : d111537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99283, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99283, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99284 q = 1) (hb : d107483 q = 1) : d111538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99284, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99284, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99291 q = 1) (hb : d107483 q = 1) : d111545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99291, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99291, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17240 q ha hb
  have h11 (q : Pattern) (ha : d99292 q = 1) (hb : d107483 q = 1) : d111546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99292, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99292, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99293 q = 1) (hb : d107483 q = 1) : d111547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99293, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99293, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99294 q = 1) (hb : d107483 q = 1) : d111548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99294, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99294, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99295 q = 1) (hb : d107483 q = 1) : d111549 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99295, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99295, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99296 q = 1) (hb : d107483 q = 1) : d111550 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99296, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99296, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17242 (p : Pattern) (ha : d99302 p = 1) (hb : d107483 p = 1) : d111556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99297 q = 1) (hb : d107483 q = 1) : d111551 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99297, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99297, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17241 q ha hb
  have h2 (q : Pattern) (ha : d99298 q = 1) (hb : d107483 q = 1) : d111552 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99298, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99298, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99299 q = 1) (hb : d107483 q = 1) : d111553 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99299, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99299, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99300 q = 1) (hb : d107483 q = 1) : d111554 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99300, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99300, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99301 q = 1) (hb : d107483 q = 1) : d111555 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99301, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99301, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99302 q = 1) (hb : d107483 q = 1) : d111556 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99302, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99302, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17243 (p : Pattern) (ha : d99308 p = 1) (hb : d107483 p = 1) : d111562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7898 q = 1) (hb : d107483 q = 1) : d111154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16977 q ha hb
    | true =>
      simp only [d7898, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16968 q ha hb
  have h2 (q : Pattern) (ha : d7899 q = 1) (hb : d107483 q = 1) : d111155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7900 q = 1) (hb : d107483 q = 1) : d111156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7900, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7901 q = 1) (hb : d107483 q = 1) : d111157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7902 q = 1) (hb : d107483 q = 1) : d111158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99308 q = 1) (hb : d107483 q = 1) : d111562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99308, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99308, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17244 (p : Pattern) (ha : d99319 p = 1) (hb : d107483 p = 1) : d111573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99314 q = 1) (hb : d107483 q = 1) : d111568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99314, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16999 q ha hb
    | true =>
      simp only [d99314, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16972 q ha hb
  have h2 (q : Pattern) (ha : d99315 q = 1) (hb : d107483 q = 1) : d111569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99315, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99315, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99316 q = 1) (hb : d107483 q = 1) : d111570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99316, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99316, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99317 q = 1) (hb : d107483 q = 1) : d111571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99317, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99317, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99318 q = 1) (hb : d107483 q = 1) : d111572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99318, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99318, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99319 q = 1) (hb : d107483 q = 1) : d111573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99319, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99319, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17245 (p : Pattern) (ha : d99325 p = 1) (hb : d107483 p = 1) : d111579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d107483 q = 1) : d111160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16976 q ha hb
    | true =>
      simp only [d7904, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16978 q ha hb
  have h2 (q : Pattern) (ha : d7905 q = 1) (hb : d107483 q = 1) : d111161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99306 q = 1) (hb : d107483 q = 1) : d111560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99306, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99306, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99307 q = 1) (hb : d107483 q = 1) : d111561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99307, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99307, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99309 q = 1) (hb : d107483 q = 1) : d111563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99309, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99309, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17243 q ha hb
  have h6 (q : Pattern) (ha : d99310 q = 1) (hb : d107483 q = 1) : d111564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99310, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99310, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99311 q = 1) (hb : d107483 q = 1) : d111565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99311, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99311, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99312 q = 1) (hb : d107483 q = 1) : d111566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99312, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99312, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99313 q = 1) (hb : d107483 q = 1) : d111567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99313, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99313, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99320 q = 1) (hb : d107483 q = 1) : d111574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99320, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99320, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17244 q ha hb
  have h11 (q : Pattern) (ha : d99321 q = 1) (hb : d107483 q = 1) : d111575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99321, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99321, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99322 q = 1) (hb : d107483 q = 1) : d111576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99322, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99322, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99323 q = 1) (hb : d107483 q = 1) : d111577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99323, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99323, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99324 q = 1) (hb : d107483 q = 1) : d111578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99324, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99324, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99325 q = 1) (hb : d107483 q = 1) : d111579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99325, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99325, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro17246 (p : Pattern) (ha : d99331 p = 1) (hb : d107483 p = 1) : d111585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99326 q = 1) (hb : d107483 q = 1) : d111580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99326, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99326, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17245 q ha hb
  have h2 (q : Pattern) (ha : d99327 q = 1) (hb : d107483 q = 1) : d111581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99327, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99327, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99328 q = 1) (hb : d107483 q = 1) : d111582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99328, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99328, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99329 q = 1) (hb : d107483 q = 1) : d111583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99329, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99329, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99330 q = 1) (hb : d107483 q = 1) : d111584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99330, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99330, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99331 q = 1) (hb : d107483 q = 1) : d111585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99331, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99331, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17247 (p : Pattern) (ha : d99338 p = 1) (hb : d107483 p = 1) : d111592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8053 q = 1) (hb : d107483 q = 1) : d111289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17015 q ha hb
    | true =>
      simp only [d8053, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17006 q ha hb
  have h2 (q : Pattern) (ha : d8054 q = 1) (hb : d107483 q = 1) : d111290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8055 q = 1) (hb : d107483 q = 1) : d111291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8055, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8056 q = 1) (hb : d107483 q = 1) : d111292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8057 q = 1) (hb : d107483 q = 1) : d111293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99338 q = 1) (hb : d107483 q = 1) : d111592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99338, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99338, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17248 (p : Pattern) (ha : d99349 p = 1) (hb : d107483 p = 1) : d111603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d99344 q = 1) (hb : d107483 q = 1) : d111598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99344, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17037 q ha hb
    | true =>
      simp only [d99344, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17010 q ha hb
  have h2 (q : Pattern) (ha : d99345 q = 1) (hb : d107483 q = 1) : d111599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99345, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99345, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d99346 q = 1) (hb : d107483 q = 1) : d111600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99346, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99346, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99347 q = 1) (hb : d107483 q = 1) : d111601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99347, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99347, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99348 q = 1) (hb : d107483 q = 1) : d111602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99348, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99348, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d99349 q = 1) (hb : d107483 q = 1) : d111603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99349, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99349, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro17249 (p : Pattern) (ha : d99355 p = 1) (hb : d107483 p = 1) : d111609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d107483 q = 1) : d111295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17014 q ha hb
    | true =>
      simp only [d8059, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17016 q ha hb
  have h2 (q : Pattern) (ha : d8060 q = 1) (hb : d107483 q = 1) : d111296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d99336 q = 1) (hb : d107483 q = 1) : d111590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99336, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99336, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d99337 q = 1) (hb : d107483 q = 1) : d111591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99337, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99337, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d99339 q = 1) (hb : d107483 q = 1) : d111593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99339, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99339, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17247 q ha hb
  have h6 (q : Pattern) (ha : d99340 q = 1) (hb : d107483 q = 1) : d111594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99340, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99340, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d99341 q = 1) (hb : d107483 q = 1) : d111595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99341, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99341, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d99342 q = 1) (hb : d107483 q = 1) : d111596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99342, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99342, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d99343 q = 1) (hb : d107483 q = 1) : d111597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99343, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99343, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d99350 q = 1) (hb : d107483 q = 1) : d111604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99350, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99350, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17248 q ha hb
  have h11 (q : Pattern) (ha : d99351 q = 1) (hb : d107483 q = 1) : d111605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99351, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99351, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d99352 q = 1) (hb : d107483 q = 1) : d111606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99352, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99352, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d99353 q = 1) (hb : d107483 q = 1) : d111607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99353, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99353, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d99354 q = 1) (hb : d107483 q = 1) : d111608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99354, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99354, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d99355 q = 1) (hb : d107483 q = 1) : d111609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99355, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99355, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
