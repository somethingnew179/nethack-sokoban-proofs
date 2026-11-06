import NetHack.Soko22Hazard87.AndIntroBlocks0419
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro105000 (p : Pattern) (ha : d319123 p = 1) (hb : d322099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45345 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45345, d319095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104997 q ha hb
    | true =>
      simp only [d45345, d319095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104969 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319096 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319096, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319096, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45351 q = 1) (hb : d319098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45351, d319098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104998 q ha hb
    | true =>
      simp only [d45351, d319098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45352 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45352, d319099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45352, d319099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319100 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319100, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319100, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319121 q = 1) (hb : d322097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319121, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319121, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319122 q = 1) (hb : d322098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319122, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319122, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319123 q = 1) (hb : d322099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319123, d322099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319123, d322099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105001 (p : Pattern) (ha : d45398 p = 1) (hb : d319145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45384 q = 1) (hb : d319131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45384, d319131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45384, d319131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
  have h2 (q : Pattern) (ha : d45241 q = 1) (hb : d319036 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
    | true =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45385 q = 1) (hb : d319132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45385, d319132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45385, d319132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45242 q = 1) (hb : d319037 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45386 q = 1) (hb : d319133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45386, d319133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45386, d319133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45387 q = 1) (hb : d319134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45387, d319134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45387, d319134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45388 q = 1) (hb : d319135 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45388, d319135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45388, d319135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
  have h8 (q : Pattern) (ha : d45246 q = 1) (hb : d319041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
    | true =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45389 q = 1) (hb : d319136 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45389, d319136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45389, d319136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45247 q = 1) (hb : d319042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45390 q = 1) (hb : d319137 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45390, d319137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45390, d319137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45391 q = 1) (hb : d319138 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45391, d319138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45391, d319138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45392 q = 1) (hb : d319139 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45392, d319139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45392, d319139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45393 q = 1) (hb : d319140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
  have h15 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45394 q = 1) (hb : d319141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45395 q = 1) (hb : d319142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45396 q = 1) (hb : d319143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d45112 q = 1) (hb : d318926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
  have h21 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45113 q = 1) (hb : d318927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d45114 q = 1) (hb : d318928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d45115 q = 1) (hb : d318929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45397 q = 1) (hb : d319144 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45397, d319144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45397, d319144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45398 q = 1) (hb : d319145 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45398, d319145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45398, d319145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105002 (p : Pattern) (ha : d45402 p = 1) (hb : d319149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45112 q = 1) (hb : d318926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d318926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
  have h2 (q : Pattern) (ha : d45013 q = 1) (hb : d318858 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104945 q ha hb
    | true =>
      simp only [d45013, d318858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45113 q = 1) (hb : d318927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45113, d318927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45014 q = 1) (hb : d318859 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45014, d318859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45114 q = 1) (hb : d318928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45114, d318928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45115 q = 1) (hb : d318929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45115, d318929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45116 q = 1) (hb : d318930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45116, d318930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45116, d318930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45402 q = 1) (hb : d319149 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45402, d319149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45402, d319149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105003 (p : Pattern) (ha : d45408 p = 1) (hb : d319155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45399 q = 1) (hb : d319146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45399, d319146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105001 q ha hb
    | true =>
      simp only [d45399, d319146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104957 q ha hb
  have h2 (q : Pattern) (ha : d45400 q = 1) (hb : d319147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45400, d319147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45400, d319147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45401 q = 1) (hb : d319148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45401, d319148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45401, d319148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45403 q = 1) (hb : d319150 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45403, d319150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104957 q ha hb
    | true =>
      simp only [d45403, d319150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105002 q ha hb
  have h5 (q : Pattern) (ha : d45404 q = 1) (hb : d319151 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45404, d319151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45404, d319151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45405 q = 1) (hb : d319152 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45405, d319152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45405, d319152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45406 q = 1) (hb : d319153 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45406, d319153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45406, d319153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45118 q = 1) (hb : d318932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104957 q ha hb
    | true =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
  have h9 (q : Pattern) (ha : d45119 q = 1) (hb : d318933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45120 q = 1) (hb : d318934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44940 q = 1) (hb : d318785 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
    | true =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h12 (q : Pattern) (ha : d44941 q = 1) (hb : d318786 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44942 q = 1) (hb : d318787 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45121 q = 1) (hb : d318935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45407 q = 1) (hb : d319154 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45407, d319154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45407, d319154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45408 q = 1) (hb : d319155 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45408, d319155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45408, d319155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105004 (p : Pattern) (ha : d45413 p = 1) (hb : d319160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45118 q = 1) (hb : d318932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104957 q ha hb
    | true =>
      simp only [d45118, d318932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
  have h2 (q : Pattern) (ha : d45119 q = 1) (hb : d318933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d318933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45120 q = 1) (hb : d318934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d318934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44940 q = 1) (hb : d318785 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104933 q ha hb
    | true =>
      simp only [d44940, d318785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d44941 q = 1) (hb : d318786 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d318786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44942 q = 1) (hb : d318787 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d318787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45121 q = 1) (hb : d318935 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45121, d318935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45411 q = 1) (hb : d319158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45411, d319158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45411, d319158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45412 q = 1) (hb : d319159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45412, d319159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45412, d319159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45413 q = 1) (hb : d319160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45413, d319160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45413, d319160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105005 (p : Pattern) (ha : d45419 p = 1) (hb : d319166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45409 q = 1) (hb : d319156 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45409, d319156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105003 q ha hb
    | true =>
      simp only [d45409, d319156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45410 q = 1) (hb : d319157 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45410, d319157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45410, d319157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45414 q = 1) (hb : d319161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105004 q ha hb
    | true =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45415 q = 1) (hb : d319162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45416 q = 1) (hb : d319163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45416, d319163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45416, d319163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45417 q = 1) (hb : d319164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45417, d319164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45417, d319164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45418 q = 1) (hb : d319165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45418, d319165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45418, d319165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45419 q = 1) (hb : d319166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45419, d319166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45419, d319166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105006 (p : Pattern) (ha : d45427 p = 1) (hb : d319174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45414 q = 1) (hb : d319161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105004 q ha hb
    | true =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45415 q = 1) (hb : d319162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45422 q = 1) (hb : d319169 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45422, d319169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104975 q ha hb
    | true =>
      simp only [d45422, d319169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45423 q = 1) (hb : d319170 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45423, d319170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45423, d319170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45424 q = 1) (hb : d319171 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45424, d319171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45424, d319171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45425 q = 1) (hb : d319172 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45425, d319172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45425, d319172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45426 q = 1) (hb : d319173 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45426, d319173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45426, d319173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45427 q = 1) (hb : d319174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45427, d319174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45427, d319174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105007 (p : Pattern) (ha : d45466 p = 1) (hb : d319185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45414 q = 1) (hb : d319161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105004 q ha hb
    | true =>
      simp only [d45414, d319161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45415 q = 1) (hb : d319162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45415, d319162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45463 q = 1) (hb : d319182 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45463, d319182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45463, d319182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45464 q = 1) (hb : d319183 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45464, d319183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45464, d319183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45465 q = 1) (hb : d319184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45465, d319184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45465, d319184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45466 q = 1) (hb : d319185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45466, d319185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45466, d319185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105008 (p : Pattern) (ha : d319191 p = 1) (hb : d322109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45428 q = 1) (hb : d319175 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45428, d319175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105005 q ha hb
    | true =>
      simp only [d45428, d319175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105006 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319180 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319181 q = 1) (hb : d322105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319181, d322105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319181, d322105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45467 q = 1) (hb : d319186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45467, d319186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105007 q ha hb
    | true =>
      simp only [d45467, d319186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45468 q = 1) (hb : d319187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45468, d319187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45468, d319187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319188 q = 1) (hb : d322106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319188, d322106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319188, d322106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319189 q = 1) (hb : d322107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319189, d322107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319189, d322107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319190 q = 1) (hb : d322108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319190, d322108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319190, d322108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319191 q = 1) (hb : d322109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319191, d322109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319191, d322109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105009 (p : Pattern) (ha : d319204 p = 1) (hb : d322115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45196 q = 1) (hb : d318991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45196, d318991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45196, d318991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104968 q ha hb
  have h2 (q : Pattern) (ha : d45197 q = 1) (hb : d318992 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45197, d318992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45197, d318992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45206 q = 1) (hb : d319001 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d319001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104968 q ha hb
    | true =>
      simp only [d45206, d319001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104971 q ha hb
  have h4 (q : Pattern) (ha : d45207 q = 1) (hb : d319002 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d319002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45207, d319002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45208 q = 1) (hb : d319003 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45208, d319003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45208, d319003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319104 q = 1) (hb : d322093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319104, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104992 q ha hb
    | true =>
      simp only [d319104, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104999 q ha hb
  have h7 (q : Pattern) (ha : d45370 q = 1) (hb : d319117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45370, d319117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104972 q ha hb
    | true =>
      simp only [d45370, d319117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104973 q ha hb
  have h8 (q : Pattern) (ha : d319118 q = 1) (hb : d322094 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319118, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319118, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d319119 q = 1) (hb : d322095 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319119, d322095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319119, d322095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319120 q = 1) (hb : d322096 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319120, d322096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d319120, d322096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319124 q = 1) (hb : d322100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319124, d322100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319124, d322100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105000 q ha hb
  have h12 (q : Pattern) (ha : d45379 q = 1) (hb : d319126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45379, d319126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45379, d319126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104974 q ha hb
  have h13 (q : Pattern) (ha : d319127 q = 1) (hb : d322101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319127, d322101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319127, d322101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319128 q = 1) (hb : d322102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319128, d322102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319128, d322102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319129 q = 1) (hb : d322103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319129, d322103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319129, d322103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319130 q = 1) (hb : d322104 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319130, d322104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319130, d322104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319192 q = 1) (hb : d322110 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319192, d322110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319192, d322110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105008 q ha hb
  have h18 (q : Pattern) (ha : d45484 q = 1) (hb : d319199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45484, d319199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45484, d319199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104977 q ha hb
  have h19 (q : Pattern) (ha : d319200 q = 1) (hb : d322111 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319200, d322111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319200, d322111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d319201 q = 1) (hb : d322112 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319201, d322112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319201, d322112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319202 q = 1) (hb : d322113 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319202, d322113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319202, d322113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319203 q = 1) (hb : d322114 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319203, d322114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319203, d322114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319204 q = 1) (hb : d322115 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319204, d322115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319204, d322115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105010 (p : Pattern) (ha : d319210 p = 1) (hb : d322121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319205 q = 1) (hb : d322116 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319205, d322116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319205, d322116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105009 q ha hb
  have h2 (q : Pattern) (ha : d319206 q = 1) (hb : d322117 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319206, d322117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319206, d322117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319207 q = 1) (hb : d322118 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319207, d322118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319207, d322118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319208 q = 1) (hb : d322119 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319208, d322119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319208, d322119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319209 q = 1) (hb : d322120 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319209, d322120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319209, d322120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319210 q = 1) (hb : d322121 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319210, d322121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319210, d322121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105011 (p : Pattern) (ha : d45497 p = 1) (hb : d319212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44888 q = 1) (hb : d318733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44889 q = 1) (hb : d318734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45497 q = 1) (hb : d319212 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45497, d319212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45497, d319212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro105012 (p : Pattern) (ha : d45503 p = 1) (hb : d319218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45241 q = 1) (hb : d319036 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
    | true =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45242 q = 1) (hb : d319037 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45243 q = 1) (hb : d319038 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45243, d319038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45243, d319038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45244 q = 1) (hb : d319039 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45244, d319039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45244, d319039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45246 q = 1) (hb : d319041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
    | true =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45247 q = 1) (hb : d319042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45248 q = 1) (hb : d319043 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45248, d319043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45248, d319043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45249 q = 1) (hb : d319044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45249, d319044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45249, d319044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45250 q = 1) (hb : d319045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45250, d319045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45250, d319045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45256 q = 1) (hb : d319051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45257 q = 1) (hb : d319052 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45500 q = 1) (hb : d319215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45501 q = 1) (hb : d319216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45502 q = 1) (hb : d319217 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45502, d319217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45502, d319217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45503 q = 1) (hb : d319218 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45503, d319218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45503, d319218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105013 (p : Pattern) (ha : d45506 p = 1) (hb : d319221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45005 q = 1) (hb : d318850 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
    | true =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45006 q = 1) (hb : d318851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45007 q = 1) (hb : d318852 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45007, d318852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45007, d318852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45008 q = 1) (hb : d318853 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45008, d318853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45008, d318853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45500 q = 1) (hb : d319215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45501 q = 1) (hb : d319216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45504 q = 1) (hb : d319219 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45504, d319219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45504, d319219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45505 q = 1) (hb : d319220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45506 q = 1) (hb : d319221 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45506, d319221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45506, d319221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105014 (p : Pattern) (ha : d45510 p = 1) (hb : d319225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45500 q = 1) (hb : d319215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45501 q = 1) (hb : d319216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45505 q = 1) (hb : d319220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45510 q = 1) (hb : d319225 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45510, d319225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45510, d319225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105015 (p : Pattern) (ha : d45517 p = 1) (hb : d319232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45507 q = 1) (hb : d319222 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45507, d319222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105012 q ha hb
    | true =>
      simp only [d45507, d319222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105013 q ha hb
  have h2 (q : Pattern) (ha : d45508 q = 1) (hb : d319223 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45508, d319223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45508, d319223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45509 q = 1) (hb : d319224 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45509, d319224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45509, d319224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45511 q = 1) (hb : d319226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105013 q ha hb
    | true =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105014 q ha hb
  have h5 (q : Pattern) (ha : d45512 q = 1) (hb : d319227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45513 q = 1) (hb : d319228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45514 q = 1) (hb : d319229 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45514, d319229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45514, d319229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45515 q = 1) (hb : d319230 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45515, d319230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45515, d319230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45516 q = 1) (hb : d319231 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45516, d319231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45516, d319231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45517 q = 1) (hb : d319232 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45517, d319232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45517, d319232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105016 (p : Pattern) (ha : d45521 p = 1) (hb : d319236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45511 q = 1) (hb : d319226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105013 q ha hb
    | true =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105014 q ha hb
  have h2 (q : Pattern) (ha : d45512 q = 1) (hb : d319227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45513 q = 1) (hb : d319228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45515 q = 1) (hb : d319230 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45515, d319230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45515, d319230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45520 q = 1) (hb : d319235 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45520, d319235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45520, d319235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45521 q = 1) (hb : d319236 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45521, d319236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45521, d319236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105017 (p : Pattern) (ha : d45527 p = 1) (hb : d319242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45525 q = 1) (hb : d319240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45526 q = 1) (hb : d319241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45526, d319241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45526, d319241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45527 q = 1) (hb : d319242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45527, d319242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45527, d319242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105018 (p : Pattern) (ha : d45531 p = 1) (hb : d319246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45529 q = 1) (hb : d319244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45530 q = 1) (hb : d319245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45530, d319245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45530, d319245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45531 q = 1) (hb : d319246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45531, d319246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45531, d319246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105019 (p : Pattern) (ha : d45537 p = 1) (hb : d319252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45532 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
    | true =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
  have h2 (q : Pattern) (ha : d45533 q = 1) (hb : d319248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45534 q = 1) (hb : d319249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45535 q = 1) (hb : d319250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45536 q = 1) (hb : d319251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45537 q = 1) (hb : d319252 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45537, d319252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45537, d319252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105020 (p : Pattern) (ha : d45540 p = 1) (hb : d319255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45525 q = 1) (hb : d319240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45526 q = 1) (hb : d319241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45526, d319241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45526, d319241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45540 q = 1) (hb : d319255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45540, d319255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45540, d319255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105021 (p : Pattern) (ha : d45541 p = 1) (hb : d319256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45529 q = 1) (hb : d319244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45530 q = 1) (hb : d319245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45530, d319245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45530, d319245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45541 q = 1) (hb : d319256 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45541, d319256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45541, d319256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105022 (p : Pattern) (ha : d45547 p = 1) (hb : d319262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45532 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
    | true =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
  have h2 (q : Pattern) (ha : d45533 q = 1) (hb : d319248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45534 q = 1) (hb : d319249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45535 q = 1) (hb : d319250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45536 q = 1) (hb : d319251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45542 q = 1) (hb : d319257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105020 q ha hb
    | true =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105021 q ha hb
  have h7 (q : Pattern) (ha : d45543 q = 1) (hb : d319258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d319258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45543, d319258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45544 q = 1) (hb : d319259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d319259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45544, d319259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45545 q = 1) (hb : d319260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d319260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d319260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45546 q = 1) (hb : d319261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d319261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d319261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45547 q = 1) (hb : d319262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45547, d319262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45547, d319262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105023 (p : Pattern) (ha : d45738 p = 1) (hb : d319382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45532 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
    | true =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
  have h2 (q : Pattern) (ha : d45533 q = 1) (hb : d319248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45533, d319248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45534 q = 1) (hb : d319249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45534, d319249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45535 q = 1) (hb : d319250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45535, d319250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45536 q = 1) (hb : d319251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45536, d319251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45733 q = 1) (hb : d319377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45733, d319377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
    | true =>
      simp only [d45733, d319377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45734 q = 1) (hb : d319378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45734, d319378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45734, d319378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45735 q = 1) (hb : d319379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45735, d319379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45735, d319379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45736 q = 1) (hb : d319380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45736, d319380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45736, d319380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45737 q = 1) (hb : d319381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45737, d319381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45737, d319381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45738 q = 1) (hb : d319382 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45738, d319382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45738, d319382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105024 (p : Pattern) (ha : d45744 p = 1) (hb : d319388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45733 q = 1) (hb : d319377 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45733, d319377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
    | true =>
      simp only [d45733, d319377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45734 q = 1) (hb : d319378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45734, d319378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45734, d319378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45735 q = 1) (hb : d319379 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45735, d319379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45735, d319379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45736 q = 1) (hb : d319380 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45736, d319380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45736, d319380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45737 q = 1) (hb : d319381 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45737, d319381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45737, d319381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45739 q = 1) (hb : d319383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45739, d319383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105021 q ha hb
    | true =>
      simp only [d45739, d319383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45740 q = 1) (hb : d319384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45740, d319384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45740, d319384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45741 q = 1) (hb : d319385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45741, d319385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45741, d319385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45742 q = 1) (hb : d319386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45742, d319386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45742, d319386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45743 q = 1) (hb : d319387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45743, d319387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45743, d319387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45744 q = 1) (hb : d319388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45744, d319388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45744, d319388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105025 (p : Pattern) (ha : d45753 p = 1) (hb : d319397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45739 q = 1) (hb : d319383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45739, d319383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105021 q ha hb
    | true =>
      simp only [d45739, d319383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45740 q = 1) (hb : d319384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45740, d319384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45740, d319384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45741 q = 1) (hb : d319385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45741, d319385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45741, d319385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45742 q = 1) (hb : d319386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45742, d319386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45742, d319386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45743 q = 1) (hb : d319387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45743, d319387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45743, d319387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45753 q = 1) (hb : d319397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45753, d319397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45753, d319397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105026 (p : Pattern) (ha : d45790 p = 1) (hb : d319434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45107 q = 1) (hb : d318921 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45107, d318921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45107, d318921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
  have h2 (q : Pattern) (ha : d45005 q = 1) (hb : d318850 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104944 q ha hb
    | true =>
      simp only [d45005, d318850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45108 q = 1) (hb : d318922 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45108, d318922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45108, d318922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45006 q = 1) (hb : d318851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45006, d318851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45109 q = 1) (hb : d318923 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45109, d318923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45109, d318923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45110 q = 1) (hb : d318924 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45110, d318924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45110, d318924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45774 q = 1) (hb : d319418 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
  have h8 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45775 q = 1) (hb : d319419 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45776 q = 1) (hb : d319420 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45777 q = 1) (hb : d319421 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45789 q = 1) (hb : d319433 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45789, d319433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45789, d319433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45783 q = 1) (hb : d319427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45790 q = 1) (hb : d319434 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45790, d319434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45790, d319434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105027 (p : Pattern) (ha : d45794 p = 1) (hb : d319438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45774 q = 1) (hb : d319418 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
  have h2 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45775 q = 1) (hb : d319419 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45776 q = 1) (hb : d319420 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45777 q = 1) (hb : d319421 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45783 q = 1) (hb : d319427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45794 q = 1) (hb : d319438 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45794, d319438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45794, d319438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105028 (p : Pattern) (ha : d45813 p = 1) (hb : d319457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45795 q = 1) (hb : d319439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105026 q ha hb
    | true =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105027 q ha hb
  have h2 (q : Pattern) (ha : d45796 q = 1) (hb : d319440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45797 q = 1) (hb : d319441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45803 q = 1) (hb : d319447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45803, d319447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45803, d319447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45812 q = 1) (hb : d319456 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45812, d319456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45812, d319456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45813 q = 1) (hb : d319457 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45813, d319457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45813, d319457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105029 (p : Pattern) (ha : d45884 p = 1) (hb : d319468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45814 q = 1) (hb : d319458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45814, d319458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105028 q ha hb
    | true =>
      simp only [d45814, d319458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45815 q = 1) (hb : d319459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45815, d319459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45815, d319459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45881 q = 1) (hb : d319465 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45881, d319465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45881, d319465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45882 q = 1) (hb : d319466 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45882, d319466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45882, d319466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45883 q = 1) (hb : d319467 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45883, d319467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45883, d319467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45884 q = 1) (hb : d319468 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45884, d319468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45884, d319468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105030 (p : Pattern) (ha : d45890 p = 1) (hb : d319487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45885 q = 1) (hb : d319482 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45885, d319482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105029 q ha hb
    | true =>
      simp only [d45885, d319482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45886 q = 1) (hb : d319483 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45886, d319483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45886, d319483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45887 q = 1) (hb : d319484 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45887, d319484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45887, d319484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45888 q = 1) (hb : d319485 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45888, d319485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45888, d319485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45889 q = 1) (hb : d319486 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45889, d319486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45889, d319486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45890 q = 1) (hb : d319487 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45890, d319487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45890, d319487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105031 (p : Pattern) (ha : d45552 p = 1) (hb : d319267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45525 q = 1) (hb : d319240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45551 q = 1) (hb : d319266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45551, d319266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45551, d319266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45552 q = 1) (hb : d319267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45552, d319267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45552, d319267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105032 (p : Pattern) (ha : d45554 p = 1) (hb : d319269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45529 q = 1) (hb : d319244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45553 q = 1) (hb : d319268 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45553, d319268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45553, d319268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45554 q = 1) (hb : d319269 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45554, d319269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45554, d319269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105033 (p : Pattern) (ha : d45561 p = 1) (hb : d319276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45559 q = 1) (hb : d319274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45559, d319274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45559, d319274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45560 q = 1) (hb : d319275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45560, d319275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45560, d319275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45561 q = 1) (hb : d319276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45561, d319276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45561, d319276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105034 (p : Pattern) (ha : d45564 p = 1) (hb : d319279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45562 q = 1) (hb : d319277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45562, d319277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45562, d319277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45563 q = 1) (hb : d319278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45563, d319278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45563, d319278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45564 q = 1) (hb : d319279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45564, d319279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45564, d319279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105035 (p : Pattern) (ha : d45582 p = 1) (hb : d319297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d319023 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d319024 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45568 q = 1) (hb : d319283 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45568, d319283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45568, d319283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45577 q = 1) (hb : d319292 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45577, d319292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45577, d319292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45578 q = 1) (hb : d319293 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45578, d319293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45578, d319293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45230 q = 1) (hb : d319025 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45579 q = 1) (hb : d319294 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45579, d319294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45579, d319294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45580 q = 1) (hb : d319295 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45580, d319295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45580, d319295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45581 q = 1) (hb : d319296 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45581, d319296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45581, d319296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45582 q = 1) (hb : d319297 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45582, d319297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45582, d319297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105036 (p : Pattern) (ha : d45596 p = 1) (hb : d319311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d319023 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d319024 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44999 q = 1) (hb : d318844 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d44999, d318844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45000 q = 1) (hb : d318845 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45000, d318845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45230 q = 1) (hb : d319025 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45230, d319025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104983 q ha hb
    | true =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d319032 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45238 q = 1) (hb : d319033 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45238, d319033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45238, d319033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45239 q = 1) (hb : d319034 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45239, d319034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45239, d319034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45591 q = 1) (hb : d319306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45592 q = 1) (hb : d319307 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45593 q = 1) (hb : d319308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45593, d319308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45593, d319308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d45594 q = 1) (hb : d319309 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45594, d319309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45594, d319309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d45595 q = 1) (hb : d319310 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45595, d319310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45595, d319310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45596 q = 1) (hb : d319311 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45596, d319311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45596, d319311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105037 (p : Pattern) (ha : d45605 p = 1) (hb : d319320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d319023 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45228, d319023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d319024 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, d319024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45591 q = 1) (hb : d319306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45592 q = 1) (hb : d319307 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45602 q = 1) (hb : d319317 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45602, d319317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45602, d319317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45603 q = 1) (hb : d319318 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45603, d319318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45603, d319318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45604 q = 1) (hb : d319319 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45604, d319319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45604, d319319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45593 q = 1) (hb : d319308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45593, d319308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45593, d319308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45594 q = 1) (hb : d319309 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45594, d319309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45594, d319309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45595 q = 1) (hb : d319310 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45595, d319310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45595, d319310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45605 q = 1) (hb : d319320 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45605, d319320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45605, d319320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro105038 (p : Pattern) (ha : d45611 p = 1) (hb : d319326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45583 q = 1) (hb : d319298 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45583, d319298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105035 q ha hb
    | true =>
      simp only [d45583, d319298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45584 q = 1) (hb : d319299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45584, d319299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45584, d319299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45585 q = 1) (hb : d319300 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45585, d319300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45585, d319300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45586 q = 1) (hb : d319301 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45586, d319301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45586, d319301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45597 q = 1) (hb : d319312 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45597, d319312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105036 q ha hb
    | true =>
      simp only [d45597, d319312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45598 q = 1) (hb : d319313 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45598, d319313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45598, d319313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45599 q = 1) (hb : d319314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45599, d319314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45599, d319314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45600 q = 1) (hb : d319315 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45600, d319315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45600, d319315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45601 q = 1) (hb : d319316 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45601, d319316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45601, d319316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45606 q = 1) (hb : d319321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45606, d319321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105037 q ha hb
    | true =>
      simp only [d45606, d319321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45607 q = 1) (hb : d319322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45607, d319322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45607, d319322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45608 q = 1) (hb : d319323 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45608, d319323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45608, d319323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45609 q = 1) (hb : d319324 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45609, d319324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45609, d319324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45256 q = 1) (hb : d319051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45257 q = 1) (hb : d319052 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45610 q = 1) (hb : d319325 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45610, d319325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45610, d319325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45611 q = 1) (hb : d319326 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45611, d319326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45611, d319326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105039 (p : Pattern) (ha : d45615 p = 1) (hb : d319330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45256 q = 1) (hb : d319051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d319051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45257 q = 1) (hb : d319052 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45257, d319052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45500 q = 1) (hb : d319215 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45500, d319215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45501 q = 1) (hb : d319216 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45501, d319216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45502 q = 1) (hb : d319217 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45502, d319217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45502, d319217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45505 q = 1) (hb : d319220 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45505, d319220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45615 q = 1) (hb : d319330 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45615, d319330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45615, d319330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105040 (p : Pattern) (ha : d45621 p = 1) (hb : d319336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45612 q = 1) (hb : d319327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45612, d319327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105038 q ha hb
    | true =>
      simp only [d45612, d319327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105012 q ha hb
  have h2 (q : Pattern) (ha : d45613 q = 1) (hb : d319328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45613, d319328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45613, d319328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45614 q = 1) (hb : d319329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45614, d319329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45614, d319329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45616 q = 1) (hb : d319331 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45616, d319331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105012 q ha hb
    | true =>
      simp only [d45616, d319331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105039 q ha hb
  have h5 (q : Pattern) (ha : d45617 q = 1) (hb : d319332 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45617, d319332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45617, d319332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45618 q = 1) (hb : d319333 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45618, d319333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45618, d319333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45619 q = 1) (hb : d319334 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45619, d319334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45619, d319334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45507 q = 1) (hb : d319222 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45507, d319222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105012 q ha hb
    | true =>
      simp only [d45507, d319222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105013 q ha hb
  have h9 (q : Pattern) (ha : d45508 q = 1) (hb : d319223 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45508, d319223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45508, d319223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45509 q = 1) (hb : d319224 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45509, d319224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45509, d319224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45511 q = 1) (hb : d319226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105013 q ha hb
    | true =>
      simp only [d45511, d319226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105014 q ha hb
  have h12 (q : Pattern) (ha : d45512 q = 1) (hb : d319227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45512, d319227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45513 q = 1) (hb : d319228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45513, d319228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45514 q = 1) (hb : d319229 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45514, d319229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45514, d319229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45620 q = 1) (hb : d319335 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45620, d319335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45620, d319335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45621 q = 1) (hb : d319336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45621, d319336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45621, d319336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105041 (p : Pattern) (ha : d45627 p = 1) (hb : d319342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45622 q = 1) (hb : d319337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45622, d319337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105040 q ha hb
    | true =>
      simp only [d45622, d319337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45623 q = 1) (hb : d319338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45623, d319338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45623, d319338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45624 q = 1) (hb : d319339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45624, d319339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45624, d319339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45625 q = 1) (hb : d319340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45625, d319340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45625, d319340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45626 q = 1) (hb : d319341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45626, d319341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45626, d319341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45627 q = 1) (hb : d319342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45627, d319342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45627, d319342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105042 (p : Pattern) (ha : d45701 p = 1) (hb : d319348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45698 q = 1) (hb : d319345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45698, d319345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45698, d319345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45699 q = 1) (hb : d319346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45699, d319346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45699, d319346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45700 q = 1) (hb : d319347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45700, d319347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45700, d319347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45701 q = 1) (hb : d319348 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45701, d319348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45701, d319348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105043 (p : Pattern) (ha : d319354 p = 1) (hb : d322127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45555 q = 1) (hb : d319270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45555, d319270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105031 q ha hb
    | true =>
      simp only [d45555, d319270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105032 q ha hb
  have h2 (q : Pattern) (ha : d45556 q = 1) (hb : d319271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45556, d319271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45556, d319271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45557 q = 1) (hb : d319272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45557, d319272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45557, d319272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45558 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45558, d319273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45558, d319273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45565 q = 1) (hb : d319280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45565, d319280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105033 q ha hb
    | true =>
      simp only [d45565, d319280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105034 q ha hb
  have h6 (q : Pattern) (ha : d45566 q = 1) (hb : d319281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45566, d319281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45566, d319281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45567 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45567, d319282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45567, d319282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45628 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45628, d319343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105041 q ha hb
    | true =>
      simp only [d45628, d319343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319344 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319344, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45702 q = 1) (hb : d319349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45702, d319349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105042 q ha hb
    | true =>
      simp only [d45702, d319349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45703 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45703, d319350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45703, d319350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319351 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319351, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319352 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319352, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319353 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319353, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319354 q = 1) (hb : d322127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319354, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319354, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro105044 (p : Pattern) (ha : d45708 p = 1) (hb : d319355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45525 q = 1) (hb : d319240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45525, d319240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45551 q = 1) (hb : d319266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45551, d319266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45551, d319266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45708 q = 1) (hb : d319355 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45708, d319355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45708, d319355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105045 (p : Pattern) (ha : d45709 p = 1) (hb : d319356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45529 q = 1) (hb : d319244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45529, d319244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45553 q = 1) (hb : d319268 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45553, d319268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45553, d319268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45709 q = 1) (hb : d319356 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45709, d319356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45709, d319356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105046 (p : Pattern) (ha : d45714 p = 1) (hb : d319361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45524 q = 1) (hb : d319239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45524, d319239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45559 q = 1) (hb : d319274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45559, d319274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45559, d319274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45560 q = 1) (hb : d319275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45560, d319275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45560, d319275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45714 q = 1) (hb : d319361 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45714, d319361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45714, d319361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105047 (p : Pattern) (ha : d45715 p = 1) (hb : d319362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45522 q = 1) (hb : d319237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105016 q ha hb
    | true =>
      simp only [d45522, d319237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45523 q = 1) (hb : d319238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45523, d319238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45528 q = 1) (hb : d319243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45528, d319243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45562 q = 1) (hb : d319277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45562, d319277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45562, d319277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45563 q = 1) (hb : d319278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45563, d319278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45563, d319278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45715 q = 1) (hb : d319362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45715, d319362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45715, d319362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105048 (p : Pattern) (ha : d45719 p = 1) (hb : d319366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45622 q = 1) (hb : d319337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45622, d319337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105040 q ha hb
    | true =>
      simp only [d45622, d319337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45623 q = 1) (hb : d319338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45623, d319338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45623, d319338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45624 q = 1) (hb : d319339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45624, d319339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45624, d319339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45625 q = 1) (hb : d319340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45625, d319340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45625, d319340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45626 q = 1) (hb : d319341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45626, d319341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45626, d319341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45719 q = 1) (hb : d319366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45719, d319366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45719, d319366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105049 (p : Pattern) (ha : d45725 p = 1) (hb : d319369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45518 q = 1) (hb : d319233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105015 q ha hb
    | true =>
      simp only [d45518, d319233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45519 q = 1) (hb : d319234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45519, d319234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45698 q = 1) (hb : d319345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45698, d319345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45698, d319345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45699 q = 1) (hb : d319346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45699, d319346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45699, d319346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45700 q = 1) (hb : d319347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45700, d319347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45700, d319347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45725 q = 1) (hb : d319369 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45725, d319369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45725, d319369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105050 (p : Pattern) (ha : d319375 p = 1) (hb : d322132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45555 q = 1) (hb : d319270 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45555, d319270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105031 q ha hb
    | true =>
      simp only [d45555, d319270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105032 q ha hb
  have h2 (q : Pattern) (ha : d45556 q = 1) (hb : d319271 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45556, d319271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45556, d319271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45557 q = 1) (hb : d319272 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45557, d319272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45557, d319272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45558 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45558, d319273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45558, d319273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45565 q = 1) (hb : d319280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45565, d319280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105033 q ha hb
    | true =>
      simp only [d45565, d319280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105034 q ha hb
  have h6 (q : Pattern) (ha : d45566 q = 1) (hb : d319281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45566, d319281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45566, d319281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45567 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45567, d319282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45567, d319282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45628 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45628, d319343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105041 q ha hb
    | true =>
      simp only [d45628, d319343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319344 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319344, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319344, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d45702 q = 1) (hb : d319349 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45702, d319349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105042 q ha hb
    | true =>
      simp only [d45702, d319349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45703 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45703, d319350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45703, d319350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319351 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319351, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319351, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319352 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319352, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319352, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319353 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319353, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319353, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45710 q = 1) (hb : d319357 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45710, d319357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105044 q ha hb
    | true =>
      simp only [d45710, d319357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105045 q ha hb
  have h17 (q : Pattern) (ha : d45711 q = 1) (hb : d319358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45711, d319358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45711, d319358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45712 q = 1) (hb : d319359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45712, d319359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45712, d319359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45713 q = 1) (hb : d319360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45713, d319360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45713, d319360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d45716 q = 1) (hb : d319363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45716, d319363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105046 q ha hb
    | true =>
      simp only [d45716, d319363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105047 q ha hb
  have h21 (q : Pattern) (ha : d45717 q = 1) (hb : d319364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45717, d319364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45717, d319364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d45718 q = 1) (hb : d319365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45718, d319365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45718, d319365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d45720 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45720, d319367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105048 q ha hb
    | true =>
      simp only [d45720, d319367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105020 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d319257 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d319368 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d319368, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d45726 q = 1) (hb : d319370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45726, d319370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105049 q ha hb
    | true =>
      simp only [d45726, d319370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d45727 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45727, d319371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d45727, d319371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d319372 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d319372, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d319373 q = 1) (hb : d322130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319373, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d319373, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d319374 q = 1) (hb : d322131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319374, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d319374, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d319375 q = 1) (hb : d322132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319375, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319375, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro105051 (p : Pattern) (ha : d319395 p = 1) (hb : d322139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45720 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45720, d319367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105048 q ha hb
    | true =>
      simp only [d45720, d319367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105020 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319368 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319368, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319368, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45726 q = 1) (hb : d319370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45726, d319370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105049 q ha hb
    | true =>
      simp only [d45726, d319370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45727 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45727, d319371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45727, d319371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319372 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319372, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319372, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319393 q = 1) (hb : d322137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319393, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319393, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319394 q = 1) (hb : d322138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319394, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319394, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319395 q = 1) (hb : d322139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319395, d322139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319395, d322139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105052 (p : Pattern) (ha : d45773 p = 1) (hb : d319417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45759 q = 1) (hb : d319403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45759, d319403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45759, d319403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105035 q ha hb
  have h2 (q : Pattern) (ha : d45583 q = 1) (hb : d319298 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45583, d319298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105035 q ha hb
    | true =>
      simp only [d45583, d319298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45760 q = 1) (hb : d319404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45760, d319404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45760, d319404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45584 q = 1) (hb : d319299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45584, d319299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45584, d319299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45761 q = 1) (hb : d319405 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45761, d319405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45761, d319405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45762 q = 1) (hb : d319406 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45762, d319406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45762, d319406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45763 q = 1) (hb : d319407 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45763, d319407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45763, d319407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105036 q ha hb
  have h8 (q : Pattern) (ha : d45597 q = 1) (hb : d319312 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45597, d319312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105036 q ha hb
    | true =>
      simp only [d45597, d319312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45764 q = 1) (hb : d319408 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45764, d319408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45764, d319408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45598 q = 1) (hb : d319313 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45598, d319313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45598, d319313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45765 q = 1) (hb : d319409 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45765, d319409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45765, d319409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45766 q = 1) (hb : d319410 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45766, d319410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45766, d319410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45767 q = 1) (hb : d319411 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45767, d319411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45767, d319411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45768 q = 1) (hb : d319412 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45768, d319412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45768, d319412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105037 q ha hb
  have h15 (q : Pattern) (ha : d45606 q = 1) (hb : d319321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45606, d319321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105037 q ha hb
    | true =>
      simp only [d45606, d319321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45769 q = 1) (hb : d319413 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45769, d319413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45769, d319413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45607 q = 1) (hb : d319322 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45607, d319322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45607, d319322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45770 q = 1) (hb : d319414 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45770, d319414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45770, d319414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45771 q = 1) (hb : d319415 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45771, d319415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45771, d319415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d45393 q = 1) (hb : d319140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
  have h21 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45394 q = 1) (hb : d319141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d45395 q = 1) (hb : d319142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d45396 q = 1) (hb : d319143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45772 q = 1) (hb : d319416 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45772, d319416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45772, d319416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45773 q = 1) (hb : d319417 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45773, d319417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45773, d319417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105053 (p : Pattern) (ha : d45779 p = 1) (hb : d319423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45384 q = 1) (hb : d319131 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45384, d319131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45384, d319131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
  have h2 (q : Pattern) (ha : d45241 q = 1) (hb : d319036 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104984 q ha hb
    | true =>
      simp only [d45241, d319036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45385 q = 1) (hb : d319132 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45385, d319132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45385, d319132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45242 q = 1) (hb : d319037 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45242, d319037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45386 q = 1) (hb : d319133 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45386, d319133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45386, d319133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45387 q = 1) (hb : d319134 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45387, d319134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45387, d319134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45388 q = 1) (hb : d319135 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45388, d319135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45388, d319135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
  have h8 (q : Pattern) (ha : d45246 q = 1) (hb : d319041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104985 q ha hb
    | true =>
      simp only [d45246, d319041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45389 q = 1) (hb : d319136 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45389, d319136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45389, d319136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45247 q = 1) (hb : d319042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45247, d319042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45390 q = 1) (hb : d319137 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45390, d319137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45390, d319137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45391 q = 1) (hb : d319138 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45391, d319138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45391, d319138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45392 q = 1) (hb : d319139 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45392, d319139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45392, d319139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45393 q = 1) (hb : d319140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
  have h15 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45394 q = 1) (hb : d319141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45395 q = 1) (hb : d319142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45396 q = 1) (hb : d319143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d45774 q = 1) (hb : d319418 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
  have h21 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45775 q = 1) (hb : d319419 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d45776 q = 1) (hb : d319420 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d45777 q = 1) (hb : d319421 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45778 q = 1) (hb : d319422 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45778, d319422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45778, d319422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45779 q = 1) (hb : d319423 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45779, d319423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45779, d319423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105054 (p : Pattern) (ha : d45784 p = 1) (hb : d319428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45393 q = 1) (hb : d319140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45393, d319140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
  have h2 (q : Pattern) (ha : d45254 q = 1) (hb : d319049 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104986 q ha hb
    | true =>
      simp only [d45254, d319049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45394 q = 1) (hb : d319141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45394, d319141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45255 q = 1) (hb : d319050 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45255, d319050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45395 q = 1) (hb : d319142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45395, d319142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45396 q = 1) (hb : d319143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45396, d319143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45774 q = 1) (hb : d319418 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45774, d319418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
  have h8 (q : Pattern) (ha : d45498 q = 1) (hb : d319213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105011 q ha hb
    | true =>
      simp only [d45498, d319213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45775 q = 1) (hb : d319419 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45775, d319419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45499 q = 1) (hb : d319214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45499, d319214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45776 q = 1) (hb : d319420 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45776, d319420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45777 q = 1) (hb : d319421 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45777, d319421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45778 q = 1) (hb : d319422 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45778, d319422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45778, d319422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45783 q = 1) (hb : d319427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45783, d319427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45784 q = 1) (hb : d319428 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45784, d319428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45784, d319428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105055 (p : Pattern) (ha : d45800 p = 1) (hb : d319444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45780 q = 1) (hb : d319424 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45780, d319424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105052 q ha hb
    | true =>
      simp only [d45780, d319424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105053 q ha hb
  have h2 (q : Pattern) (ha : d45781 q = 1) (hb : d319425 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45781, d319425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45781, d319425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45782 q = 1) (hb : d319426 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45782, d319426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45782, d319426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45785 q = 1) (hb : d319429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45785, d319429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105053 q ha hb
    | true =>
      simp only [d45785, d319429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105054 q ha hb
  have h5 (q : Pattern) (ha : d45786 q = 1) (hb : d319430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45786, d319430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45786, d319430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45787 q = 1) (hb : d319431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45787, d319431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45787, d319431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45788 q = 1) (hb : d319432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45788, d319432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45788, d319432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45791 q = 1) (hb : d319435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45791, d319435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105053 q ha hb
    | true =>
      simp only [d45791, d319435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105026 q ha hb
  have h9 (q : Pattern) (ha : d45792 q = 1) (hb : d319436 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45792, d319436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45792, d319436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45793 q = 1) (hb : d319437 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45793, d319437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45793, d319437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45795 q = 1) (hb : d319439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105026 q ha hb
    | true =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105027 q ha hb
  have h12 (q : Pattern) (ha : d45796 q = 1) (hb : d319440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45797 q = 1) (hb : d319441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45798 q = 1) (hb : d319442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45798, d319442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45798, d319442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45799 q = 1) (hb : d319443 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45799, d319443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45799, d319443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45800 q = 1) (hb : d319444 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45800, d319444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45800, d319444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105056 (p : Pattern) (ha : d45805 p = 1) (hb : d319449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45791 q = 1) (hb : d319435 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45791, d319435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105053 q ha hb
    | true =>
      simp only [d45791, d319435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105026 q ha hb
  have h2 (q : Pattern) (ha : d45792 q = 1) (hb : d319436 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45792, d319436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45792, d319436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45793 q = 1) (hb : d319437 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45793, d319437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45793, d319437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45795 q = 1) (hb : d319439 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105026 q ha hb
    | true =>
      simp only [d45795, d319439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105027 q ha hb
  have h5 (q : Pattern) (ha : d45796 q = 1) (hb : d319440 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45796, d319440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45797 q = 1) (hb : d319441 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45797, d319441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45798 q = 1) (hb : d319442 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45798, d319442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45798, d319442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45803 q = 1) (hb : d319447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45803, d319447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45803, d319447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45804 q = 1) (hb : d319448 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45804, d319448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45804, d319448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45805 q = 1) (hb : d319449 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45805, d319449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45805, d319449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105057 (p : Pattern) (ha : d45811 p = 1) (hb : d319455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45801 q = 1) (hb : d319445 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45801, d319445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105055 q ha hb
    | true =>
      simp only [d45801, d319445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45802 q = 1) (hb : d319446 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45802, d319446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45802, d319446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45806 q = 1) (hb : d319450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105056 q ha hb
    | true =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45807 q = 1) (hb : d319451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45808 q = 1) (hb : d319452 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45808, d319452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45808, d319452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45809 q = 1) (hb : d319453 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45809, d319453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45809, d319453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45810 q = 1) (hb : d319454 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45810, d319454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45810, d319454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45811 q = 1) (hb : d319455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45811, d319455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45811, d319455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105058 (p : Pattern) (ha : d45819 p = 1) (hb : d319463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45806 q = 1) (hb : d319450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105056 q ha hb
    | true =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45807 q = 1) (hb : d319451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45814 q = 1) (hb : d319458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45814, d319458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105028 q ha hb
    | true =>
      simp only [d45814, d319458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45815 q = 1) (hb : d319459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45815, d319459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45815, d319459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45816 q = 1) (hb : d319460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45816, d319460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45816, d319460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45817 q = 1) (hb : d319461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45817, d319461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45817, d319461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45818 q = 1) (hb : d319462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45818, d319462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45818, d319462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45819 q = 1) (hb : d319463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45819, d319463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45819, d319463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105059 (p : Pattern) (ha : d45873 p = 1) (hb : d319474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45806 q = 1) (hb : d319450 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105056 q ha hb
    | true =>
      simp only [d45806, d319450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45807 q = 1) (hb : d319451 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45807, d319451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45870 q = 1) (hb : d319471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45870, d319471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45870, d319471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45871 q = 1) (hb : d319472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45871, d319472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45871, d319472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45872 q = 1) (hb : d319473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45872, d319473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45872, d319473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45873 q = 1) (hb : d319474 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45873, d319474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45873, d319474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105060 (p : Pattern) (ha : d319480 p = 1) (hb : d322149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45820 q = 1) (hb : d319464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45820, d319464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105057 q ha hb
    | true =>
      simp only [d45820, d319464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105058 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319470 q = 1) (hb : d322145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319470, d322145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319470, d322145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45874 q = 1) (hb : d319475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45874, d319475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105059 q ha hb
    | true =>
      simp only [d45874, d319475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45875 q = 1) (hb : d319476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45875, d319476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45875, d319476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319477 q = 1) (hb : d322146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319477, d322146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319477, d322146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319478 q = 1) (hb : d322147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319478, d322147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319478, d322147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319479 q = 1) (hb : d322148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319479, d322148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319479, d322148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319480 q = 1) (hb : d322149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319480, d322149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319480, d322149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105061 (p : Pattern) (ha : d319493 p = 1) (hb : d322155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45538 q = 1) (hb : d319253 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45538, d319253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45538, d319253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105019 q ha hb
  have h2 (q : Pattern) (ha : d45539 q = 1) (hb : d319254 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45539, d319254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45539, d319254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45548 q = 1) (hb : d319263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d319263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105019 q ha hb
    | true =>
      simp only [d45548, d319263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105022 q ha hb
  have h4 (q : Pattern) (ha : d45549 q = 1) (hb : d319264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d319264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45549, d319264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45550 q = 1) (hb : d319265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d45550, d319265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45550, d319265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319376 q = 1) (hb : d322133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319376, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105043 q ha hb
    | true =>
      simp only [d319376, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105050 q ha hb
  have h7 (q : Pattern) (ha : d45745 q = 1) (hb : d319389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45745, d319389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105023 q ha hb
    | true =>
      simp only [d45745, d319389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105024 q ha hb
  have h8 (q : Pattern) (ha : d319390 q = 1) (hb : d322134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319390, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319390, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d319391 q = 1) (hb : d322135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319391, d322135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319391, d322135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319392 q = 1) (hb : d322136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319392, d322136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d319392, d322136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319396 q = 1) (hb : d322140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319396, d322140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319396, d322140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105051 q ha hb
  have h12 (q : Pattern) (ha : d45754 q = 1) (hb : d319398 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45754, d319398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45754, d319398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105025 q ha hb
  have h13 (q : Pattern) (ha : d319399 q = 1) (hb : d322141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319399, d322141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319399, d322141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319400 q = 1) (hb : d322142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319400, d322142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319400, d322142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319401 q = 1) (hb : d322143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319401, d322143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319401, d322143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319402 q = 1) (hb : d322144 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319402, d322144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319402, d322144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319481 q = 1) (hb : d322150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319481, d322150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319481, d322150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105060 q ha hb
  have h18 (q : Pattern) (ha : d45891 q = 1) (hb : d319488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45891, d319488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45891, d319488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105030 q ha hb
  have h19 (q : Pattern) (ha : d319489 q = 1) (hb : d322151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319489, d322151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319489, d322151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d319490 q = 1) (hb : d322152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319490, d322152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319490, d322152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319491 q = 1) (hb : d322153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319491, d322153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319491, d322153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319492 q = 1) (hb : d322154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319492, d322154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319492, d322154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319493 q = 1) (hb : d322155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319493, d322155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319493, d322155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105062 (p : Pattern) (ha : d319499 p = 1) (hb : d322161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319494 q = 1) (hb : d322156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319494, d322156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319494, d322156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105061 q ha hb
  have h2 (q : Pattern) (ha : d319495 q = 1) (hb : d322157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319495, d322157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319495, d322157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319496 q = 1) (hb : d322158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319496, d322158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319496, d322158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319497 q = 1) (hb : d322159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319497, d322159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319497, d322159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319498 q = 1) (hb : d322160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319498, d322160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319498, d322160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319499 q = 1) (hb : d322161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319499, d322161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319499, d322161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105063 (p : Pattern) (ha : d45915 p = 1) (hb : d319512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45907 q = 1) (hb : d319504 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45908 q = 1) (hb : d319505 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45909 q = 1) (hb : d319506 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45910 q = 1) (hb : d319507 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h12 (q : Pattern) (ha : d45911 q = 1) (hb : d319508 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45912 q = 1) (hb : d319509 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45579 q = 1) (hb : d319294 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45579, d319294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45579, d319294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45913 q = 1) (hb : d319510 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45913, d319510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45913, d319510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45914 q = 1) (hb : d319511 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45914, d319511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45914, d319511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45915 q = 1) (hb : d319512 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45915, d319512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45915, d319512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105064 (p : Pattern) (ha : d45927 p = 1) (hb : d319524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45910 q = 1) (hb : d319507 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d45911 q = 1) (hb : d319508 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45912 q = 1) (hb : d319509 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104983 q ha hb
    | true =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d319032 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45920 q = 1) (hb : d319517 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45920, d319517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45920, d319517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45921 q = 1) (hb : d319518 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45921, d319518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45921, d319518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d45922 q = 1) (hb : d319519 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h14 (q : Pattern) (ha : d45923 q = 1) (hb : d319520 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d45924 q = 1) (hb : d319521 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d45925 q = 1) (hb : d319522 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d45926 q = 1) (hb : d319523 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d45927 q = 1) (hb : d319524 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45927, d319524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45927, d319524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105065 (p : Pattern) (ha : d45936 p = 1) (hb : d319533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45591 q = 1) (hb : d319306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d45592 q = 1) (hb : d319307 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45933 q = 1) (hb : d319530 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45933, d319530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45933, d319530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45934 q = 1) (hb : d319531 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45934, d319531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45934, d319531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45935 q = 1) (hb : d319532 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45935, d319532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45935, d319532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d45922 q = 1) (hb : d319519 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h9 (q : Pattern) (ha : d45923 q = 1) (hb : d319520 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d45924 q = 1) (hb : d319521 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45925 q = 1) (hb : d319522 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d45926 q = 1) (hb : d319523 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d45936 q = 1) (hb : d319533 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45936, d319533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45936, d319533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105066 (p : Pattern) (ha : d45945 p = 1) (hb : d319542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45910 q = 1) (hb : d319507 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45911 q = 1) (hb : d319508 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45941 q = 1) (hb : d319538 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45941, d319538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45941, d319538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45942 q = 1) (hb : d319539 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45942, d319539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45942, d319539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45943 q = 1) (hb : d319540 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45943, d319540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45943, d319540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45944 q = 1) (hb : d319541 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45944, d319541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45944, d319541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h10 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d45945 q = 1) (hb : d319542 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45945, d319542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45945, d319542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro105067 (p : Pattern) (ha : d45951 p = 1) (hb : d319548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45916 q = 1) (hb : d319513 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45916, d319513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105063 q ha hb
    | true =>
      simp only [d45916, d319513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45917 q = 1) (hb : d319514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45917, d319514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45917, d319514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45918 q = 1) (hb : d319515 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45918, d319515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45918, d319515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45919 q = 1) (hb : d319516 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45919, d319516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45919, d319516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45928 q = 1) (hb : d319525 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45928, d319525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105064 q ha hb
    | true =>
      simp only [d45928, d319525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45929 q = 1) (hb : d319526 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45929, d319526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45929, d319526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45930 q = 1) (hb : d319527 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45930, d319527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45930, d319527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45931 q = 1) (hb : d319528 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45931, d319528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45931, d319528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45932 q = 1) (hb : d319529 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45932, d319529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45932, d319529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45937 q = 1) (hb : d319534 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
    | true =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45938 q = 1) (hb : d319535 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45939 q = 1) (hb : d319536 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45939, d319536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45939, d319536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45940 q = 1) (hb : d319537 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45940, d319537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45940, d319537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45948 q = 1) (hb : d319545 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45949 q = 1) (hb : d319546 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45950 q = 1) (hb : d319547 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45950, d319547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45950, d319547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45951 q = 1) (hb : d319548 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45951, d319548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45951, d319548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105068 (p : Pattern) (ha : d45957 p = 1) (hb : d319554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45910 q = 1) (hb : d319507 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d45911 q = 1) (hb : d319508 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45912 q = 1) (hb : d319509 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45912, d319509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d319030 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104983 q ha hb
    | true =>
      simp only [d45235, d319030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d319031 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d319031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d319032 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d319032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45920 q = 1) (hb : d319517 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45920, d319517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45920, d319517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45921 q = 1) (hb : d319518 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45921, d319518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45921, d319518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d45952 q = 1) (hb : d319549 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45952, d319549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d45952, d319549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h14 (q : Pattern) (ha : d45953 q = 1) (hb : d319550 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45953, d319550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45953, d319550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d45954 q = 1) (hb : d319551 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45954, d319551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45954, d319551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45955 q = 1) (hb : d319552 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45955, d319552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45955, d319552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d45956 q = 1) (hb : d319553 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45956, d319553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45956, d319553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d45957 q = 1) (hb : d319554 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45957, d319554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45957, d319554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro105069 (p : Pattern) (ha : d45962 p = 1) (hb : d319559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45910 q = 1) (hb : d319507 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104943 q ha hb
    | true =>
      simp only [d45910, d319507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45911 q = 1) (hb : d319508 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45911, d319508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45952 q = 1) (hb : d319549 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45952, d319549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d45952, d319549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h4 (q : Pattern) (ha : d45953 q = 1) (hb : d319550 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45953, d319550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45953, d319550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d45954 q = 1) (hb : d319551 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45954, d319551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45954, d319551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d44887 q = 1) (hb : d318732 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45955 q = 1) (hb : d319552 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45955, d319552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45955, d319552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45956 q = 1) (hb : d319553 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45956, d319553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45956, d319553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h15 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d45962 q = 1) (hb : d319559 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45962, d319559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45962, d319559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105070 (p : Pattern) (ha : d45969 p = 1) (hb : d319566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45958 q = 1) (hb : d319555 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105068 q ha hb
    | true =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45959 q = 1) (hb : d319556 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45960 q = 1) (hb : d319557 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45960, d319557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45960, d319557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45961 q = 1) (hb : d319558 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45961, d319558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45961, d319558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45965 q = 1) (hb : d319562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45966 q = 1) (hb : d319563 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45967 q = 1) (hb : d319564 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45967, d319564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45967, d319564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45948 q = 1) (hb : d319545 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45949 q = 1) (hb : d319546 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45968 q = 1) (hb : d319565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45968, d319565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45968, d319565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45969 q = 1) (hb : d319566 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45969, d319566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45969, d319566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105071 (p : Pattern) (ha : d45974 p = 1) (hb : d319571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45965 q = 1) (hb : d319562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45966 q = 1) (hb : d319563 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45973 q = 1) (hb : d319570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45973, d319570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45973, d319570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45974 q = 1) (hb : d319571 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45974, d319571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45974, d319571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105072 (p : Pattern) (ha : d45981 p = 1) (hb : d319578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45970 q = 1) (hb : d319567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105067 q ha hb
    | true =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
  have h2 (q : Pattern) (ha : d45971 q = 1) (hb : d319568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45972 q = 1) (hb : d319569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45975 q = 1) (hb : d319572 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
    | true =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105071 q ha hb
  have h5 (q : Pattern) (ha : d45976 q = 1) (hb : d319573 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45977 q = 1) (hb : d319574 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45978 q = 1) (hb : d319575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45979 q = 1) (hb : d319576 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45979, d319576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45979, d319576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45980 q = 1) (hb : d319577 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45980, d319577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45980, d319577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45981 q = 1) (hb : d319578 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45981, d319578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45981, d319578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105073 (p : Pattern) (ha : d45985 p = 1) (hb : d319582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45975 q = 1) (hb : d319572 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
    | true =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105071 q ha hb
  have h2 (q : Pattern) (ha : d45976 q = 1) (hb : d319573 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45977 q = 1) (hb : d319574 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45979 q = 1) (hb : d319576 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45979, d319576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45979, d319576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45984 q = 1) (hb : d319581 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45984, d319581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45984, d319581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45985 q = 1) (hb : d319582 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45985, d319582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45985, d319582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105074 (p : Pattern) (ha : d45991 p = 1) (hb : d319588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45989 q = 1) (hb : d319586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45990 q = 1) (hb : d319587 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45990, d319587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45990, d319587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45991 q = 1) (hb : d319588 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45991, d319588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45991, d319588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105075 (p : Pattern) (ha : d45995 p = 1) (hb : d319592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45993 q = 1) (hb : d319590 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45994 q = 1) (hb : d319591 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45994, d319591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45994, d319591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45995 q = 1) (hb : d319592 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45995, d319592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45995, d319592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105076 (p : Pattern) (ha : d46001 p = 1) (hb : d319598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45996 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
    | true =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
  have h2 (q : Pattern) (ha : d45997 q = 1) (hb : d319594 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45998 q = 1) (hb : d319595 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45999 q = 1) (hb : d319596 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46000 q = 1) (hb : d319597 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46001 q = 1) (hb : d319598 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46001, d319598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46001, d319598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105077 (p : Pattern) (ha : d46004 p = 1) (hb : d319601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45989 q = 1) (hb : d319586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45990 q = 1) (hb : d319587 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45990, d319587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45990, d319587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46004 q = 1) (hb : d319601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46004, d319601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46004, d319601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105078 (p : Pattern) (ha : d46005 p = 1) (hb : d319602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45993 q = 1) (hb : d319590 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45994 q = 1) (hb : d319591 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45994, d319591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45994, d319591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46005 q = 1) (hb : d319602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46005, d319602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46005, d319602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105079 (p : Pattern) (ha : d46011 p = 1) (hb : d319608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45996 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
    | true =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
  have h2 (q : Pattern) (ha : d45997 q = 1) (hb : d319594 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45998 q = 1) (hb : d319595 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45999 q = 1) (hb : d319596 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46000 q = 1) (hb : d319597 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46006 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105077 q ha hb
    | true =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105078 q ha hb
  have h7 (q : Pattern) (ha : d46007 q = 1) (hb : d319604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d319604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46007, d319604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46008 q = 1) (hb : d319605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d319605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46008, d319605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46009 q = 1) (hb : d319606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d319606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d319606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46010 q = 1) (hb : d319607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d319607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d319607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46011 q = 1) (hb : d319608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46011, d319608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46011, d319608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105080 (p : Pattern) (ha : d46246 p = 1) (hb : d319733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45996 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
    | true =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
  have h2 (q : Pattern) (ha : d45997 q = 1) (hb : d319594 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45997, d319594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45998 q = 1) (hb : d319595 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45998, d319595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45999 q = 1) (hb : d319596 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45999, d319596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46000 q = 1) (hb : d319597 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46000, d319597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46241 q = 1) (hb : d319728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46241, d319728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
    | true =>
      simp only [d46241, d319728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46242 q = 1) (hb : d319729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46242, d319729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46242, d319729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46243 q = 1) (hb : d319730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46243, d319730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46243, d319730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46244 q = 1) (hb : d319731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46244, d319731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46244, d319731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46245 q = 1) (hb : d319732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46245, d319732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46245, d319732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46246 q = 1) (hb : d319733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46246, d319733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46246, d319733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105081 (p : Pattern) (ha : d46252 p = 1) (hb : d319739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46241 q = 1) (hb : d319728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46241, d319728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
    | true =>
      simp only [d46241, d319728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46242 q = 1) (hb : d319729 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46242, d319729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46242, d319729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46243 q = 1) (hb : d319730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46243, d319730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46243, d319730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46244 q = 1) (hb : d319731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46244, d319731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46244, d319731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46245 q = 1) (hb : d319732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46245, d319732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46245, d319732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46247 q = 1) (hb : d319734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46247, d319734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105078 q ha hb
    | true =>
      simp only [d46247, d319734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46248 q = 1) (hb : d319735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46248, d319735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46248, d319735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46249 q = 1) (hb : d319736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46249, d319736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46249, d319736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46250 q = 1) (hb : d319737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46250, d319737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46250, d319737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46251 q = 1) (hb : d319738 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46251, d319738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46251, d319738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46252 q = 1) (hb : d319739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46252, d319739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46252, d319739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105082 (p : Pattern) (ha : d46261 p = 1) (hb : d319748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46247 q = 1) (hb : d319734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46247, d319734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105078 q ha hb
    | true =>
      simp only [d46247, d319734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46248 q = 1) (hb : d319735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46248, d319735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46248, d319735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46249 q = 1) (hb : d319736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46249, d319736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46249, d319736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46250 q = 1) (hb : d319737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46250, d319737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46250, d319737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46251 q = 1) (hb : d319738 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46251, d319738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46251, d319738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46261 q = 1) (hb : d319748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46261, d319748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46261, d319748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105083 (p : Pattern) (ha : d46324 p = 1) (hb : d319811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46315 q = 1) (hb : d319802 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46315, d319802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46315, d319802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105068 q ha hb
  have h2 (q : Pattern) (ha : d45958 q = 1) (hb : d319555 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105068 q ha hb
    | true =>
      simp only [d45958, d319555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46316 q = 1) (hb : d319803 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46316, d319803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46316, d319803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45959 q = 1) (hb : d319556 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45959, d319556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46317 q = 1) (hb : d319804 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46317, d319804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46317, d319804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46318 q = 1) (hb : d319805 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46318, d319805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46318, d319805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46319 q = 1) (hb : d319806 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
  have h8 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46320 q = 1) (hb : d319807 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46321 q = 1) (hb : d319808 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46322 q = 1) (hb : d319809 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46323 q = 1) (hb : d319810 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46323, d319810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46323, d319810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46295 q = 1) (hb : d319782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
  have h15 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46296 q = 1) (hb : d319783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46297 q = 1) (hb : d319784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46298 q = 1) (hb : d319785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46309 q = 1) (hb : d319796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d46324 q = 1) (hb : d319811 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46324, d319811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46324, d319811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro105084 (p : Pattern) (ha : d46329 p = 1) (hb : d319816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46319 q = 1) (hb : d319806 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
  have h2 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46320 q = 1) (hb : d319807 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46321 q = 1) (hb : d319808 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46322 q = 1) (hb : d319809 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46328 q = 1) (hb : d319815 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46329 q = 1) (hb : d319816 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46329, d319816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46329, d319816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105085 (p : Pattern) (ha : d46348 p = 1) (hb : d319835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46330 q = 1) (hb : d319817 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105084 q ha hb
  have h2 (q : Pattern) (ha : d46331 q = 1) (hb : d319818 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46332 q = 1) (hb : d319819 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46338 q = 1) (hb : d319825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46347 q = 1) (hb : d319834 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46347, d319834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46347, d319834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46348 q = 1) (hb : d319835 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46348, d319835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46348, d319835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105086 (p : Pattern) (ha : d46437 p = 1) (hb : d319846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46349 q = 1) (hb : d319836 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105085 q ha hb
    | true =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46350 q = 1) (hb : d319837 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46434 q = 1) (hb : d319843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46434, d319843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46434, d319843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46435 q = 1) (hb : d319844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46435, d319844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46435, d319844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46436 q = 1) (hb : d319845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46436, d319845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46436, d319845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46437 q = 1) (hb : d319846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46437, d319846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46437, d319846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105087 (p : Pattern) (ha : d46443 p = 1) (hb : d319874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46438 q = 1) (hb : d319869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46438, d319869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105086 q ha hb
    | true =>
      simp only [d46438, d319869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46439 q = 1) (hb : d319870 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46439, d319870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46439, d319870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46440 q = 1) (hb : d319871 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46440, d319871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46440, d319871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46441 q = 1) (hb : d319872 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46441, d319872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46441, d319872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46442 q = 1) (hb : d319873 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46442, d319873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46442, d319873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46443 q = 1) (hb : d319874 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46443, d319874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46443, d319874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105088 (p : Pattern) (ha : d46016 p = 1) (hb : d319613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45989 q = 1) (hb : d319586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46015 q = 1) (hb : d319612 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46015, d319612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46015, d319612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46016 q = 1) (hb : d319613 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46016, d319613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46016, d319613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105089 (p : Pattern) (ha : d46018 p = 1) (hb : d319615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45993 q = 1) (hb : d319590 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46017 q = 1) (hb : d319614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46017, d319614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46017, d319614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46018 q = 1) (hb : d319615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46018, d319615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46018, d319615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105090 (p : Pattern) (ha : d46025 p = 1) (hb : d319622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46023 q = 1) (hb : d319620 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46023, d319620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46023, d319620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46024 q = 1) (hb : d319621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46024, d319621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46024, d319621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46025 q = 1) (hb : d319622 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46025, d319622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46025, d319622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105091 (p : Pattern) (ha : d46028 p = 1) (hb : d319625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46026 q = 1) (hb : d319623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46026, d319623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46026, d319623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46027 q = 1) (hb : d319624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46027, d319624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46027, d319624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46028 q = 1) (hb : d319625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46028, d319625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46028, d319625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105092 (p : Pattern) (ha : d46035 p = 1) (hb : d319632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46032 q = 1) (hb : d319629 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46032, d319629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46032, d319629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46033 q = 1) (hb : d319630 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46033, d319630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46033, d319630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46034 q = 1) (hb : d319631 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46034, d319631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46034, d319631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h7 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45907 q = 1) (hb : d319504 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45908 q = 1) (hb : d319505 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45909 q = 1) (hb : d319506 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d46035 q = 1) (hb : d319632 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46035, d319632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46035, d319632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro105093 (p : Pattern) (ha : d46047 p = 1) (hb : d319644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45907 q = 1) (hb : d319504 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45907, d319504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45571 q = 1) (hb : d319286 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88725 q ha hb
    | true =>
      simp only [d45571, d319286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45572 q = 1) (hb : d319287 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45572, d319287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45574 q = 1) (hb : d319289 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88726 q ha hb
    | true =>
      simp only [d45574, d319289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45575 q = 1) (hb : d319290 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45575, d319290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45576 q = 1) (hb : d319291 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45576, d319291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45908 q = 1) (hb : d319505 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45908, d319505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45909 q = 1) (hb : d319506 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45909, d319506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46042 q = 1) (hb : d319639 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46042, d319639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99844 q ha hb
    | true =>
      simp only [d46042, d319639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46043 q = 1) (hb : d319640 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46043, d319640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46043, d319640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45591 q = 1) (hb : d319306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45591, d319306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45592 q = 1) (hb : d319307 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45592, d319307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46044 q = 1) (hb : d319641 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46044, d319641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46044, d319641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46045 q = 1) (hb : d319642 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46045, d319642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46045, d319642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d46046 q = 1) (hb : d319643 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46046, d319643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46046, d319643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46047 q = 1) (hb : d319644 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46047, d319644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46047, d319644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105094 (p : Pattern) (ha : d46062 p = 1) (hb : d319659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46036 q = 1) (hb : d319633 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46036, d319633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105092 q ha hb
    | true =>
      simp only [d46036, d319633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46037 q = 1) (hb : d319634 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46037, d319634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46037, d319634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46038 q = 1) (hb : d319635 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46038, d319635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46038, d319635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46039 q = 1) (hb : d319636 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46039, d319636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46039, d319636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46048 q = 1) (hb : d319645 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46048, d319645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105093 q ha hb
    | true =>
      simp only [d46048, d319645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46049 q = 1) (hb : d319646 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46049, d319646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46049, d319646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46050 q = 1) (hb : d319647 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46050, d319647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46050, d319647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46051 q = 1) (hb : d319648 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46051, d319648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46051, d319648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46052 q = 1) (hb : d319649 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46052, d319649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46052, d319649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46057 q = 1) (hb : d319654 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46057, d319654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99845 q ha hb
    | true =>
      simp only [d46057, d319654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46058 q = 1) (hb : d319655 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46058, d319655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46058, d319655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46059 q = 1) (hb : d319656 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46059, d319656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46059, d319656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46060 q = 1) (hb : d319657 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46060, d319657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46060, d319657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45937 q = 1) (hb : d319534 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
    | true =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45938 q = 1) (hb : d319535 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45939 q = 1) (hb : d319536 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45939, d319536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45939, d319536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45940 q = 1) (hb : d319537 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45940, d319537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45940, d319537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46061 q = 1) (hb : d319658 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46061, d319658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46061, d319658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46062 q = 1) (hb : d319659 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46062, d319659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46062, d319659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105095 (p : Pattern) (ha : d46069 p = 1) (hb : d319666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d45905 q = 1) (hb : d319502 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104982 q ha hb
    | true =>
      simp only [d45905, d319502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45906 q = 1) (hb : d319503 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45906, d319503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45922 q = 1) (hb : d319519 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99787 q ha hb
    | true =>
      simp only [d45922, d319519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h4 (q : Pattern) (ha : d45923 q = 1) (hb : d319520 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45923, d319520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d46066 q = 1) (hb : d319663 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46066, d319663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46066, d319663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46067 q = 1) (hb : d319664 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46067, d319664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46067, d319664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d46068 q = 1) (hb : d319665 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46068, d319665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46068, d319665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318730 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104924 q ha hb
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318731 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d45924 q = 1) (hb : d319521 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45924, d319521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45925 q = 1) (hb : d319522 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45925, d319522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d45926 q = 1) (hb : d319523 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45926, d319523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d46069 q = 1) (hb : d319666 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46069, d319666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46069, d319666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro105096 (p : Pattern) (ha : d46075 p = 1) (hb : d319672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46070 q = 1) (hb : d319667 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105095 q ha hb
    | true =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46071 q = 1) (hb : d319668 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46072 q = 1) (hb : d319669 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46072, d319669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46072, d319669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46073 q = 1) (hb : d319670 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46073, d319670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46073, d319670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45948 q = 1) (hb : d319545 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45948, d319545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45949 q = 1) (hb : d319546 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45949, d319546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46074 q = 1) (hb : d319671 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46074, d319671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46074, d319671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45968 q = 1) (hb : d319565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45968, d319565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45968, d319565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46075 q = 1) (hb : d319672 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46075, d319672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46075, d319672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105097 (p : Pattern) (ha : d46081 p = 1) (hb : d319678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46063 q = 1) (hb : d319660 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46063, d319660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105094 q ha hb
    | true =>
      simp only [d46063, d319660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105067 q ha hb
  have h2 (q : Pattern) (ha : d46064 q = 1) (hb : d319661 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46064, d319661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46064, d319661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46065 q = 1) (hb : d319662 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46065, d319662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46065, d319662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46076 q = 1) (hb : d319673 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46076, d319673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105067 q ha hb
    | true =>
      simp only [d46076, d319673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105096 q ha hb
  have h5 (q : Pattern) (ha : d46077 q = 1) (hb : d319674 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46077, d319674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46077, d319674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46078 q = 1) (hb : d319675 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46078, d319675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46078, d319675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46079 q = 1) (hb : d319676 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46079, d319676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46079, d319676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45970 q = 1) (hb : d319567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105067 q ha hb
    | true =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
  have h9 (q : Pattern) (ha : d45971 q = 1) (hb : d319568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45972 q = 1) (hb : d319569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45975 q = 1) (hb : d319572 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
    | true =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105071 q ha hb
  have h12 (q : Pattern) (ha : d45976 q = 1) (hb : d319573 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45977 q = 1) (hb : d319574 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45978 q = 1) (hb : d319575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46080 q = 1) (hb : d319677 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46080, d319677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46080, d319677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46081 q = 1) (hb : d319678 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46081, d319678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46081, d319678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105098 (p : Pattern) (ha : d46087 p = 1) (hb : d319684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46082 q = 1) (hb : d319679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46082, d319679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105097 q ha hb
    | true =>
      simp only [d46082, d319679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46083 q = 1) (hb : d319680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46083, d319680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46083, d319680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46084 q = 1) (hb : d319681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46084, d319681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46084, d319681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46085 q = 1) (hb : d319682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46085, d319682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46085, d319682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46086 q = 1) (hb : d319683 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46086, d319683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46086, d319683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46087 q = 1) (hb : d319684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46087, d319684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46087, d319684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105099 (p : Pattern) (ha : d46197 p = 1) (hb : d319687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45965 q = 1) (hb : d319562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45965, d319562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45966 q = 1) (hb : d319563 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45966, d319563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45973 q = 1) (hb : d319570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45973, d319570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45973, d319570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46197 q = 1) (hb : d319687 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46197, d319687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46197, d319687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105100 (p : Pattern) (ha : d46203 p = 1) (hb : d319693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45970 q = 1) (hb : d319567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105067 q ha hb
    | true =>
      simp only [d45970, d319567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
  have h2 (q : Pattern) (ha : d45971 q = 1) (hb : d319568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45971, d319568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45972 q = 1) (hb : d319569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45972, d319569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45975 q = 1) (hb : d319572 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
    | true =>
      simp only [d45975, d319572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105071 q ha hb
  have h5 (q : Pattern) (ha : d45976 q = 1) (hb : d319573 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45976, d319573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45977 q = 1) (hb : d319574 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45977, d319574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45978 q = 1) (hb : d319575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45978, d319575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46198 q = 1) (hb : d319688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46198, d319688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105070 q ha hb
    | true =>
      simp only [d46198, d319688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105099 q ha hb
  have h9 (q : Pattern) (ha : d46199 q = 1) (hb : d319689 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46199, d319689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46199, d319689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46200 q = 1) (hb : d319690 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46200, d319690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46200, d319690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46201 q = 1) (hb : d319691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46201, d319691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46201, d319691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46202 q = 1) (hb : d319692 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46202, d319692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46202, d319692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46203 q = 1) (hb : d319693 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46203, d319693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46203, d319693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105101 (p : Pattern) (ha : d46209 p = 1) (hb : d319699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46204 q = 1) (hb : d319694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46204, d319694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105100 q ha hb
    | true =>
      simp only [d46204, d319694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46205 q = 1) (hb : d319695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46205, d319695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46205, d319695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46206 q = 1) (hb : d319696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46206, d319696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46206, d319696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46207 q = 1) (hb : d319697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46207, d319697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46207, d319697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46208 q = 1) (hb : d319698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46208, d319698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46208, d319698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46209 q = 1) (hb : d319699 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46209, d319699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46209, d319699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105102 (p : Pattern) (ha : d319705 p = 1) (hb : d322168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46019 q = 1) (hb : d319616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46019, d319616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105088 q ha hb
    | true =>
      simp only [d46019, d319616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105089 q ha hb
  have h2 (q : Pattern) (ha : d46020 q = 1) (hb : d319617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46020, d319617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46020, d319617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46021 q = 1) (hb : d319618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46021, d319618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46021, d319618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46022 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46022, d319619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46022, d319619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46029 q = 1) (hb : d319626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46029, d319626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105090 q ha hb
    | true =>
      simp only [d46029, d319626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105091 q ha hb
  have h6 (q : Pattern) (ha : d46030 q = 1) (hb : d319627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46030, d319627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46030, d319627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46031 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46031, d319628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46031, d319628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46088 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46088, d319685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105098 q ha hb
    | true =>
      simp only [d46088, d319685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319686 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319686, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d46210 q = 1) (hb : d319700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46210, d319700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105101 q ha hb
    | true =>
      simp only [d46210, d319700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46211 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46211, d319701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46211, d319701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319702 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319702, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319703 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319703, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319704 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319704, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d319705 q = 1) (hb : d322168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319705, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319705, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro105103 (p : Pattern) (ha : d46216 p = 1) (hb : d319706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45989 q = 1) (hb : d319586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45989, d319586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46015 q = 1) (hb : d319612 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46015, d319612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46015, d319612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46216 q = 1) (hb : d319706 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46216, d319706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46216, d319706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105104 (p : Pattern) (ha : d46217 p = 1) (hb : d319707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45993 q = 1) (hb : d319590 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45993, d319590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46017 q = 1) (hb : d319614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46017, d319614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46017, d319614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46217 q = 1) (hb : d319707 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46217, d319707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46217, d319707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105105 (p : Pattern) (ha : d46222 p = 1) (hb : d319712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45988 q = 1) (hb : d319585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45988, d319585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46023 q = 1) (hb : d319620 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46023, d319620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46023, d319620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46024 q = 1) (hb : d319621 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46024, d319621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46024, d319621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46222 q = 1) (hb : d319712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46222, d319712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46222, d319712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105106 (p : Pattern) (ha : d46223 p = 1) (hb : d319713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45986 q = 1) (hb : d319583 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105073 q ha hb
    | true =>
      simp only [d45986, d319583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45987 q = 1) (hb : d319584 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45987, d319584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45992 q = 1) (hb : d319589 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45992, d319589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46026 q = 1) (hb : d319623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46026, d319623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46026, d319623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46027 q = 1) (hb : d319624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46027, d319624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46027, d319624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46223 q = 1) (hb : d319713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46223, d319713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46223, d319713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105107 (p : Pattern) (ha : d46227 p = 1) (hb : d319717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46082 q = 1) (hb : d319679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46082, d319679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105097 q ha hb
    | true =>
      simp only [d46082, d319679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46083 q = 1) (hb : d319680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46083, d319680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46083, d319680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45982 q = 1) (hb : d319579 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105072 q ha hb
    | true =>
      simp only [d45982, d319579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45983 q = 1) (hb : d319580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45983, d319580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46084 q = 1) (hb : d319681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46084, d319681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46084, d319681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46085 q = 1) (hb : d319682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46085, d319682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46085, d319682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46086 q = 1) (hb : d319683 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46086, d319683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46086, d319683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46227 q = 1) (hb : d319717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46227, d319717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46227, d319717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105108 (p : Pattern) (ha : d46233 p = 1) (hb : d319720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46204 q = 1) (hb : d319694 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46204, d319694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105100 q ha hb
    | true =>
      simp only [d46204, d319694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46205 q = 1) (hb : d319695 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46205, d319695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46205, d319695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46206 q = 1) (hb : d319696 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46206, d319696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46206, d319696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46207 q = 1) (hb : d319697 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46207, d319697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46207, d319697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46208 q = 1) (hb : d319698 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46208, d319698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46208, d319698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46233 q = 1) (hb : d319720 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46233, d319720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46233, d319720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105109 (p : Pattern) (ha : d319726 p = 1) (hb : d322173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46019 q = 1) (hb : d319616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46019, d319616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105088 q ha hb
    | true =>
      simp only [d46019, d319616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105089 q ha hb
  have h2 (q : Pattern) (ha : d46020 q = 1) (hb : d319617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46020, d319617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46020, d319617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46021 q = 1) (hb : d319618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46021, d319618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46021, d319618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46022 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46022, d319619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46022, d319619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46029 q = 1) (hb : d319626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46029, d319626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105090 q ha hb
    | true =>
      simp only [d46029, d319626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105091 q ha hb
  have h6 (q : Pattern) (ha : d46030 q = 1) (hb : d319627 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46030, d319627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46030, d319627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46031 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46031, d319628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46031, d319628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46088 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46088, d319685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105098 q ha hb
    | true =>
      simp only [d46088, d319685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d319686 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319686, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d319686, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d46210 q = 1) (hb : d319700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46210, d319700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105101 q ha hb
    | true =>
      simp only [d46210, d319700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46211 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46211, d319701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46211, d319701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d319702 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319702, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319702, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319703 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319703, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d319703, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d319704 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319704, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319704, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46218 q = 1) (hb : d319708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46218, d319708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105103 q ha hb
    | true =>
      simp only [d46218, d319708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105104 q ha hb
  have h17 (q : Pattern) (ha : d46219 q = 1) (hb : d319709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46219, d319709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46219, d319709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46220 q = 1) (hb : d319710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46220, d319710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d46220, d319710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d46221 q = 1) (hb : d319711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46221, d319711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46221, d319711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d46224 q = 1) (hb : d319714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46224, d319714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105105 q ha hb
    | true =>
      simp only [d46224, d319714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105106 q ha hb
  have h21 (q : Pattern) (ha : d46225 q = 1) (hb : d319715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46225, d319715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46225, d319715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d46226 q = 1) (hb : d319716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46226, d319716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d46226, d319716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d46228 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46228, d319718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105107 q ha hb
    | true =>
      simp only [d46228, d319718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105077 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d319719 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d319719, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d46234 q = 1) (hb : d319721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46234, d319721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105108 q ha hb
    | true =>
      simp only [d46234, d319721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d46235 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46235, d319722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d46235, d319722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d319723 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d319723, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d319724 q = 1) (hb : d322171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319724, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d319724, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d319725 q = 1) (hb : d322172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319725, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d319725, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d319726 q = 1) (hb : d322173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319726, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319726, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro105110 (p : Pattern) (ha : d319746 p = 1) (hb : d322180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46228 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46228, d319718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105107 q ha hb
    | true =>
      simp only [d46228, d319718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105077 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319719 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319719, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319719, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d46234 q = 1) (hb : d319721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46234, d319721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105108 q ha hb
    | true =>
      simp only [d46234, d319721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46235 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46235, d319722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46235, d319722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319723 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319723, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319723, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319744 q = 1) (hb : d322178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319744, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319744, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319745 q = 1) (hb : d322179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319745, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319745, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319746 q = 1) (hb : d322180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319746, d322180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319746, d322180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105111 (p : Pattern) (ha : d46285 p = 1) (hb : d319772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46267 q = 1) (hb : d319754 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46267, d319754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46267, d319754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105092 q ha hb
  have h2 (q : Pattern) (ha : d46036 q = 1) (hb : d319633 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46036, d319633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105092 q ha hb
    | true =>
      simp only [d46036, d319633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46268 q = 1) (hb : d319755 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46268, d319755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46268, d319755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46037 q = 1) (hb : d319634 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46037, d319634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46037, d319634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46269 q = 1) (hb : d319756 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46269, d319756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46269, d319756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46270 q = 1) (hb : d319757 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46270, d319757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46270, d319757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46271 q = 1) (hb : d319758 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46271, d319758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46271, d319758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105093 q ha hb
  have h8 (q : Pattern) (ha : d46048 q = 1) (hb : d319645 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46048, d319645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105093 q ha hb
    | true =>
      simp only [d46048, d319645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46272 q = 1) (hb : d319759 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46272, d319759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46272, d319759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46049 q = 1) (hb : d319646 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46049, d319646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46049, d319646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46273 q = 1) (hb : d319760 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46273, d319760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46273, d319760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46274 q = 1) (hb : d319761 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46274, d319761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46274, d319761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46275 q = 1) (hb : d319762 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46275, d319762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46275, d319762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46276 q = 1) (hb : d319763 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46276, d319763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46276, d319763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99845 q ha hb
  have h15 (q : Pattern) (ha : d46057 q = 1) (hb : d319654 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46057, d319654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro99845 q ha hb
    | true =>
      simp only [d46057, d319654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46277 q = 1) (hb : d319764 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46277, d319764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46277, d319764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46058 q = 1) (hb : d319655 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46058, d319655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46058, d319655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46278 q = 1) (hb : d319765 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46278, d319765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46278, d319765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46279 q = 1) (hb : d319766 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46279, d319766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46279, d319766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46280 q = 1) (hb : d319767 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46280, d319767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46280, d319767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
  have h21 (q : Pattern) (ha : d45937 q = 1) (hb : d319534 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
    | true =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46281 q = 1) (hb : d319768 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46281, d319768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46281, d319768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45938 q = 1) (hb : d319535 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d46282 q = 1) (hb : d319769 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46282, d319769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d46282, d319769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d46283 q = 1) (hb : d319770 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46283, d319770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46283, d319770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46284 q = 1) (hb : d319771 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46284, d319771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46284, d319771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d46285 q = 1) (hb : d319772 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46285, d319772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46285, d319772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105112 (p : Pattern) (ha : d46300 p = 1) (hb : d319787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46286 q = 1) (hb : d319773 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46286, d319773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46286, d319773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105063 q ha hb
  have h2 (q : Pattern) (ha : d45916 q = 1) (hb : d319513 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45916, d319513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105063 q ha hb
    | true =>
      simp only [d45916, d319513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46287 q = 1) (hb : d319774 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46287, d319774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46287, d319774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45917 q = 1) (hb : d319514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45917, d319514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45917, d319514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46288 q = 1) (hb : d319775 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46288, d319775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46288, d319775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46289 q = 1) (hb : d319776 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46289, d319776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46289, d319776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46290 q = 1) (hb : d319777 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46290, d319777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46290, d319777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105064 q ha hb
  have h8 (q : Pattern) (ha : d45928 q = 1) (hb : d319525 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45928, d319525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105064 q ha hb
    | true =>
      simp only [d45928, d319525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46291 q = 1) (hb : d319778 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46291, d319778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46291, d319778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45929 q = 1) (hb : d319526 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45929, d319526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45929, d319526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46292 q = 1) (hb : d319779 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46292, d319779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46292, d319779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46293 q = 1) (hb : d319780 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46293, d319780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46293, d319780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46294 q = 1) (hb : d319781 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46294, d319781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46294, d319781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46280 q = 1) (hb : d319767 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46280, d319767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46280, d319767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
  have h15 (q : Pattern) (ha : d45937 q = 1) (hb : d319534 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105065 q ha hb
    | true =>
      simp only [d45937, d319534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46281 q = 1) (hb : d319768 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46281, d319768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46281, d319768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45938 q = 1) (hb : d319535 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45938, d319535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46282 q = 1) (hb : d319769 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46282, d319769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46282, d319769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46283 q = 1) (hb : d319770 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46283, d319770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46283, d319770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46295 q = 1) (hb : d319782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
  have h21 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46296 q = 1) (hb : d319783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d46297 q = 1) (hb : d319784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d46298 q = 1) (hb : d319785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46299 q = 1) (hb : d319786 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46299, d319786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46299, d319786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d46300 q = 1) (hb : d319787 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46300, d319787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46300, d319787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105113 (p : Pattern) (ha : d46310 p = 1) (hb : d319797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46304 q = 1) (hb : d319791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46304, d319791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46304, d319791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105095 q ha hb
  have h2 (q : Pattern) (ha : d46070 q = 1) (hb : d319667 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105095 q ha hb
    | true =>
      simp only [d46070, d319667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46305 q = 1) (hb : d319792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46305, d319792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46305, d319792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46071 q = 1) (hb : d319668 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46071, d319668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46306 q = 1) (hb : d319793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46306, d319793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46306, d319793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46307 q = 1) (hb : d319794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46307, d319794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46307, d319794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46295 q = 1) (hb : d319782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46295, d319782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
  have h8 (q : Pattern) (ha : d45946 q = 1) (hb : d319543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105066 q ha hb
    | true =>
      simp only [d45946, d319543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46296 q = 1) (hb : d319783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46296, d319783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45947 q = 1) (hb : d319544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45947, d319544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46297 q = 1) (hb : d319784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46297, d319784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46298 q = 1) (hb : d319785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46298, d319785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46308 q = 1) (hb : d319795 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46308, d319795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46308, d319795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46309 q = 1) (hb : d319796 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46309, d319796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46310 q = 1) (hb : d319797 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46310, d319797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46310, d319797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105114 (p : Pattern) (ha : d46335 p = 1) (hb : d319822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46301 q = 1) (hb : d319788 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46301, d319788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105111 q ha hb
    | true =>
      simp only [d46301, d319788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105112 q ha hb
  have h2 (q : Pattern) (ha : d46302 q = 1) (hb : d319789 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46302, d319789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46302, d319789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46303 q = 1) (hb : d319790 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46303, d319790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46303, d319790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46311 q = 1) (hb : d319798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46311, d319798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105112 q ha hb
    | true =>
      simp only [d46311, d319798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105113 q ha hb
  have h5 (q : Pattern) (ha : d46312 q = 1) (hb : d319799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46312, d319799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46312, d319799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46313 q = 1) (hb : d319800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46313, d319800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46313, d319800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46314 q = 1) (hb : d319801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46314, d319801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46314, d319801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46325 q = 1) (hb : d319812 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105112 q ha hb
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
  have h9 (q : Pattern) (ha : d46326 q = 1) (hb : d319813 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46327 q = 1) (hb : d319814 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46330 q = 1) (hb : d319817 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105084 q ha hb
  have h12 (q : Pattern) (ha : d46331 q = 1) (hb : d319818 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46332 q = 1) (hb : d319819 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46333 q = 1) (hb : d319820 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46334 q = 1) (hb : d319821 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46334, d319821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46334, d319821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46335 q = 1) (hb : d319822 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46335, d319822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46335, d319822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105115 (p : Pattern) (ha : d46340 p = 1) (hb : d319827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46325 q = 1) (hb : d319812 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105112 q ha hb
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
  have h2 (q : Pattern) (ha : d46326 q = 1) (hb : d319813 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46327 q = 1) (hb : d319814 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46330 q = 1) (hb : d319817 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105084 q ha hb
  have h5 (q : Pattern) (ha : d46331 q = 1) (hb : d319818 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46332 q = 1) (hb : d319819 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46333 q = 1) (hb : d319820 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46338 q = 1) (hb : d319825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46338, d319825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46339 q = 1) (hb : d319826 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46339, d319826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46339, d319826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46340 q = 1) (hb : d319827 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46340, d319827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46340, d319827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105116 (p : Pattern) (ha : d46346 p = 1) (hb : d319833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46336 q = 1) (hb : d319823 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46336, d319823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105114 q ha hb
    | true =>
      simp only [d46336, d319823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46337 q = 1) (hb : d319824 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46337, d319824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46337, d319824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46341 q = 1) (hb : d319828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105115 q ha hb
    | true =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46342 q = 1) (hb : d319829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46343 q = 1) (hb : d319830 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46343, d319830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46343, d319830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46344 q = 1) (hb : d319831 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46344, d319831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46344, d319831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46345 q = 1) (hb : d319832 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46345, d319832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46345, d319832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46346 q = 1) (hb : d319833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46346, d319833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46346, d319833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105117 (p : Pattern) (ha : d46354 p = 1) (hb : d319841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46341 q = 1) (hb : d319828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105115 q ha hb
    | true =>
      simp only [d46341, d319828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46342 q = 1) (hb : d319829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46342, d319829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46349 q = 1) (hb : d319836 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105085 q ha hb
    | true =>
      simp only [d46349, d319836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46350 q = 1) (hb : d319837 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46350, d319837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46351 q = 1) (hb : d319838 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46351, d319838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46351, d319838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46352 q = 1) (hb : d319839 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46352, d319839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46352, d319839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46353 q = 1) (hb : d319840 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46353, d319840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46353, d319840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46354 q = 1) (hb : d319841 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46354, d319841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46354, d319841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105118 (p : Pattern) (ha : d46414 p = 1) (hb : d319849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46319 q = 1) (hb : d319806 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46319, d319806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
  have h2 (q : Pattern) (ha : d45963 q = 1) (hb : d319560 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105069 q ha hb
    | true =>
      simp only [d45963, d319560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46320 q = 1) (hb : d319807 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46320, d319807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45964 q = 1) (hb : d319561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45964, d319561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46321 q = 1) (hb : d319808 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46321, d319808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46322 q = 1) (hb : d319809 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46322, d319809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46328 q = 1) (hb : d319815 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46328, d319815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46414 q = 1) (hb : d319849 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46414, d319849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46414, d319849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105119 (p : Pattern) (ha : d46420 p = 1) (hb : d319855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46325 q = 1) (hb : d319812 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105112 q ha hb
    | true =>
      simp only [d46325, d319812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
  have h2 (q : Pattern) (ha : d46326 q = 1) (hb : d319813 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46326, d319813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46327 q = 1) (hb : d319814 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46327, d319814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46330 q = 1) (hb : d319817 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
    | true =>
      simp only [d46330, d319817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105084 q ha hb
  have h5 (q : Pattern) (ha : d46331 q = 1) (hb : d319818 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46331, d319818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46332 q = 1) (hb : d319819 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46332, d319819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46333 q = 1) (hb : d319820 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46333, d319820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46415 q = 1) (hb : d319850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46415, d319850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105083 q ha hb
    | true =>
      simp only [d46415, d319850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105118 q ha hb
  have h9 (q : Pattern) (ha : d46416 q = 1) (hb : d319851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46416, d319851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46416, d319851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46417 q = 1) (hb : d319852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46417, d319852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46417, d319852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46418 q = 1) (hb : d319853 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46418, d319853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46418, d319853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46419 q = 1) (hb : d319854 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46419, d319854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46419, d319854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46420 q = 1) (hb : d319855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46420, d319855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46420, d319855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105120 (p : Pattern) (ha : d46426 p = 1) (hb : d319861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46421 q = 1) (hb : d319856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46421, d319856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105119 q ha hb
    | true =>
      simp only [d46421, d319856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46422 q = 1) (hb : d319857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46422, d319857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46422, d319857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46423 q = 1) (hb : d319858 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46423, d319858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46423, d319858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46424 q = 1) (hb : d319859 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46424, d319859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46424, d319859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46425 q = 1) (hb : d319860 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46425, d319860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46425, d319860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46426 q = 1) (hb : d319861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46426, d319861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46426, d319861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105121 (p : Pattern) (ha : d319867 p = 1) (hb : d322190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46355 q = 1) (hb : d319842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46355, d319842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105116 q ha hb
    | true =>
      simp only [d46355, d319842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105117 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d319848 q = 1) (hb : d322186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319848, d322186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319848, d322186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d46427 q = 1) (hb : d319862 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46427, d319862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105120 q ha hb
    | true =>
      simp only [d46427, d319862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46428 q = 1) (hb : d319863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46428, d319863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46428, d319863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d319864 q = 1) (hb : d322187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319864, d322187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319864, d322187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d319865 q = 1) (hb : d322188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319865, d322188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319865, d322188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319866 q = 1) (hb : d322189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319866, d322189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319866, d322189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d319867 q = 1) (hb : d322190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319867, d322190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319867, d322190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105122 (p : Pattern) (ha : d319880 p = 1) (hb : d322196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46002 q = 1) (hb : d319599 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46002, d319599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46002, d319599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105076 q ha hb
  have h2 (q : Pattern) (ha : d46003 q = 1) (hb : d319600 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46003, d319600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46003, d319600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46012 q = 1) (hb : d319609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d319609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105076 q ha hb
    | true =>
      simp only [d46012, d319609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105079 q ha hb
  have h4 (q : Pattern) (ha : d46013 q = 1) (hb : d319610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d319610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46013, d319610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46014 q = 1) (hb : d319611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46014, d319611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46014, d319611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319727 q = 1) (hb : d322174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319727, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105102 q ha hb
    | true =>
      simp only [d319727, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105109 q ha hb
  have h7 (q : Pattern) (ha : d46253 q = 1) (hb : d319740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46253, d319740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105080 q ha hb
    | true =>
      simp only [d46253, d319740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105081 q ha hb
  have h8 (q : Pattern) (ha : d319741 q = 1) (hb : d322175 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319741, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319741, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d319742 q = 1) (hb : d322176 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319742, d322176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d319742, d322176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d319743 q = 1) (hb : d322177 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319743, d322177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d319743, d322177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d319747 q = 1) (hb : d322181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319747, d322181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319747, d322181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105110 q ha hb
  have h12 (q : Pattern) (ha : d46262 q = 1) (hb : d319749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46262, d319749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46262, d319749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105082 q ha hb
  have h13 (q : Pattern) (ha : d319750 q = 1) (hb : d322182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319750, d322182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d319750, d322182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d319751 q = 1) (hb : d322183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319751, d322183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319751, d322183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d319752 q = 1) (hb : d322184 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319752, d322184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d319752, d322184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d319753 q = 1) (hb : d322185 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319753, d322185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319753, d322185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d319868 q = 1) (hb : d322191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319868, d322191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319868, d322191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105121 q ha hb
  have h18 (q : Pattern) (ha : d46444 q = 1) (hb : d319875 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46444, d319875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46444, d319875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105087 q ha hb
  have h19 (q : Pattern) (ha : d319876 q = 1) (hb : d322192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319876, d322192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319876, d322192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d319877 q = 1) (hb : d322193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319877, d322193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d319877, d322193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d319878 q = 1) (hb : d322194 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319878, d322194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d319878, d322194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d319879 q = 1) (hb : d322195 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319879, d322195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d319879, d322195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d319880 q = 1) (hb : d322196 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319880, d322196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319880, d322196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105123 (p : Pattern) (ha : d319886 p = 1) (hb : d322202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319881 q = 1) (hb : d322197 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319881, d322197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319881, d322197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105122 q ha hb
  have h2 (q : Pattern) (ha : d319882 q = 1) (hb : d322198 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319882, d322198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319882, d322198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319883 q = 1) (hb : d322199 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319883, d322199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319883, d322199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319884 q = 1) (hb : d322200 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319884, d322200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319884, d322200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319885 q = 1) (hb : d322201 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319885, d322201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319885, d322201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319886 q = 1) (hb : d322202 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319886, d322202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319886, d322202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105124 (p : Pattern) (ha : d320471 p = 1) (hb : d322208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105123 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86233 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d322206 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d321721 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d321721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86284 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d321722 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d321722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d321723 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d321723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d321724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d322207 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d322207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d322207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d322208 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d322208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d322208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro105125 (p : Pattern) (ha : d320477 p = 1) (hb : d322214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d322209 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d322209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105124 q ha hb
    | true =>
      simp only [d320472, d322209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d322210 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d322210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d322210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d322211 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d322211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d322211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d322212 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d322212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d322212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d322213 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d322213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d322213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d322214 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d322214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d322214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105126 (p : Pattern) (ha : d320483 p = 1) (hb : d322220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d322215 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d322215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105125 q ha hb
    | true =>
      simp only [d320478, d322215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d322216 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d322216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d322216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d322217 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d322217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d322217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d322218 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d322218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d322218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d322219 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d322219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d322219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d322220 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105127 (p : Pattern) (ha : d320489 p = 1) (hb : d322226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d322221 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105126 q ha hb
    | true =>
      simp only [d320484, d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d322222 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d322223 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d322224 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d322225 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d322226 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105128 (p : Pattern) (ha : d320495 p = 1) (hb : d322232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d322227 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105127 q ha hb
    | true =>
      simp only [d320490, d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d322228 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d322229 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d322230 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d322231 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d322232 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105129 (p : Pattern) (ha : d320501 p = 1) (hb : d322238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d322233 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105128 q ha hb
    | true =>
      simp only [d320496, d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d322234 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d322235 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d322236 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d322237 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d322238 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105130 (p : Pattern) (ha : d320507 p = 1) (hb : d322244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d322239 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105129 q ha hb
    | true =>
      simp only [d320502, d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d322240 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d322241 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d322242 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d322243 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d322244 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105131 (p : Pattern) (ha : d320513 p = 1) (hb : d322250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d322245 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105130 q ha hb
    | true =>
      simp only [d320508, d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d322246 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d322247 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d322248 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d322249 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d322250 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105132 (p : Pattern) (ha : d367754 p = 1) (hb : d370801 p = 1) : d367754 p = 1 := by
  have h0 (q : Pattern) (ha : d367754 q = 1) (hb : d370801 q = 1) : d367754 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro105133 (p : Pattern) (ha : d44973 p = 1) (hb : d318887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d44969 q = 1) (hb : d318877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d318877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44969, d318877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44970 q = 1) (hb : d318884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d318884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44970, d318884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44971 q = 1) (hb : d318885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d318885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44971, d318885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44972 q = 1) (hb : d318886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d318886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44972, d318886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44973 q = 1) (hb : d318887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44973, d318887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44973, d318887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105134 (p : Pattern) (ha : d44980 p = 1) (hb : d318906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44909 q = 1) (hb : d318754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104928 q ha hb
    | true =>
      simp only [d44909, d318754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d44969 q = 1) (hb : d318877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d318877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44969, d318877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d318883 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44970 q = 1) (hb : d318884 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d318884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44970, d318884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44971 q = 1) (hb : d318885 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d318885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44971, d318885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44972 q = 1) (hb : d318886 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d318886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d318886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d318892 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d318896 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44916 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
    | true =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d44976 q = 1) (hb : d318899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d318899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44976, d318899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44977 q = 1) (hb : d318903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d318903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44977, d318903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44978 q = 1) (hb : d318904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d318904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44978, d318904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44979 q = 1) (hb : d318905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d318905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44979, d318905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44980 q = 1) (hb : d318906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44980, d318906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44980, d318906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105135 (p : Pattern) (ha : d318915 p = 1) (hb : d367603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318898 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44916 q = 1) (hb : d318761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104930 q ha hb
    | true =>
      simp only [d44916, d318761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d44976 q = 1) (hb : d318899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d318899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44976, d318899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44977 q = 1) (hb : d318903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d318903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44977, d318903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44978 q = 1) (hb : d318913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d318913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d318913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44979 q = 1) (hb : d318914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d318914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d318914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318915 q = 1) (hb : d367603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318915, d367603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318915, d367603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105136 (p : Pattern) (ha : d318955 p = 1) (hb : d367613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44952 q = 1) (hb : d318797 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d318797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104935 q ha hb
    | true =>
      simp only [d44952, d318797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d318945 q = 1) (hb : d367609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318945, d367609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318945, d367609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318951 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318952 q = 1) (hb : d367610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318952, d367610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318952, d367610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318953 q = 1) (hb : d367611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318953, d367611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318953, d367611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318954 q = 1) (hb : d367612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318954, d367612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318954, d367612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318955 q = 1) (hb : d367613 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318955, d367613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318955, d367613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105137 (p : Pattern) (ha : d318961 p = 1) (hb : d367619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318828 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44981 q = 1) (hb : d318907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d318907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105133 q ha hb
    | true =>
      simp only [d44981, d318907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105134 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44982 q = 1) (hb : d318910 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d318910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d318910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318911 q = 1) (hb : d367601 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318911, d367601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d318911, d367601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318912 q = 1) (hb : d367602 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318912, d367602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318912, d367602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318916 q = 1) (hb : d367604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318916, d367604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318916, d367604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105135 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318917 q = 1) (hb : d367605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318917, d367605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318917, d367605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d318918 q = 1) (hb : d367606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318918, d367606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318918, d367606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d318919 q = 1) (hb : d367607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318919, d367607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318919, d367607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d318920 q = 1) (hb : d367608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318920, d367608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318920, d367608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318956 q = 1) (hb : d367614 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318956, d367614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318956, d367614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105136 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318957 q = 1) (hb : d367615 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318957, d367615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318957, d367615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d318958 q = 1) (hb : d367616 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318958, d367616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318958, d367616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d318959 q = 1) (hb : d367617 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318959, d367617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318959, d367617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d318960 q = 1) (hb : d367618 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318960, d367618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318960, d367618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d318961 q = 1) (hb : d367619 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318961, d367619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318961, d367619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105138 (p : Pattern) (ha : d318967 p = 1) (hb : d367625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d318809 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d318809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86335 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d318810 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d318810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d318811 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d318811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d318812 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d318812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d318813 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d318813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318962 q = 1) (hb : d367620 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318962, d367620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318962, d367620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105137 q ha hb
  have h8 (q : Pattern) (ha : d318963 q = 1) (hb : d367621 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318963, d367621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318963, d367621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318964 q = 1) (hb : d367622 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318964, d367622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318964, d367622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318965 q = 1) (hb : d367623 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318965, d367623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318965, d367623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318966 q = 1) (hb : d367624 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318966, d367624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d318966, d367624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318967 q = 1) (hb : d367625 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318967, d367625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d318967, d367625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro105139 (p : Pattern) (ha : d45195 p = 1) (hb : d319082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45190 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
    | true =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
  have h5 (q : Pattern) (ha : d45191 q = 1) (hb : d319072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d319072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45191, d319072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45192 q = 1) (hb : d319079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d319079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45192, d319079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45193 q = 1) (hb : d319080 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d319080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45193, d319080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45194 q = 1) (hb : d319081 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d319081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45194, d319081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45195 q = 1) (hb : d319082 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45195, d319082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45195, d319082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105140 (p : Pattern) (ha : d45205 p = 1) (hb : d319103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319020 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319071 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45190 q = 1) (hb : d318985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104966 q ha hb
    | true =>
      simp only [d45190, d318985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104967 q ha hb
  have h4 (q : Pattern) (ha : d45191 q = 1) (hb : d319072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d319072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45191, d319072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319078 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45192 q = 1) (hb : d319079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d319079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45192, d319079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45193 q = 1) (hb : d319080 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d319080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45193, d319080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45194 q = 1) (hb : d319081 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d319081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d319081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319088 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319093 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d45200 q = 1) (hb : d318995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104969 q ha hb
    | true =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104970 q ha hb
  have h13 (q : Pattern) (ha : d45201 q = 1) (hb : d319096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d319096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45201, d319096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d45202 q = 1) (hb : d319100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d319100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45202, d319100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45203 q = 1) (hb : d319101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d319101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45203, d319101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45204 q = 1) (hb : d319102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d319102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45204, d319102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45205 q = 1) (hb : d319103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45205, d319103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45205, d319103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105141 (p : Pattern) (ha : d319123 p = 1) (hb : d367628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45200 q = 1) (hb : d318995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104969 q ha hb
    | true =>
      simp only [d45200, d318995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104970 q ha hb
  have h3 (q : Pattern) (ha : d45201 q = 1) (hb : d319096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d319096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45201, d319096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45202 q = 1) (hb : d319100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d319100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45202, d319100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45203 q = 1) (hb : d319121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d319121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d319121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45204 q = 1) (hb : d319122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d319122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d319122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319123 q = 1) (hb : d367628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319123, d367628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319123, d367628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105142 (p : Pattern) (ha : d319191 p = 1) (hb : d367639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319180 q = 1) (hb : d367634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319180, d367634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105006 q hb ha
    | true =>
      simp only [d319180, d367634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104976 q hb ha
  have h3 (q : Pattern) (ha : d319181 q = 1) (hb : d367635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319181, d367635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319181, d367635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319188 q = 1) (hb : d367636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319188, d367636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319188, d367636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319189 q = 1) (hb : d367637 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319189, d367637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319189, d367637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319190 q = 1) (hb : d367638 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319190, d367638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319190, d367638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319191 q = 1) (hb : d367639 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319191, d367639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319191, d367639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105143 (p : Pattern) (ha : d319204 p = 1) (hb : d367645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319003 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45206 q = 1) (hb : d319104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d319104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105139 q ha hb
    | true =>
      simp only [d45206, d319104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105140 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45207 q = 1) (hb : d319118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d319118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d319118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319119 q = 1) (hb : d367626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319119, d367626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319119, d367626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319120 q = 1) (hb : d367627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319120, d367627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319120, d367627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319124 q = 1) (hb : d367629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319124, d367629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319124, d367629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105141 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319126 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319127 q = 1) (hb : d367630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319127, d367630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319127, d367630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319128 q = 1) (hb : d367631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319128, d367631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319128, d367631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319129 q = 1) (hb : d367632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319129, d367632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319129, d367632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319130 q = 1) (hb : d367633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319130, d367633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319130, d367633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319192 q = 1) (hb : d367640 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319192, d367640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319192, d367640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105142 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319200 q = 1) (hb : d367641 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319200, d367641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319200, d367641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319201 q = 1) (hb : d367642 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319201, d367642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319201, d367642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319202 q = 1) (hb : d367643 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319202, d367643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319202, d367643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319203 q = 1) (hb : d367644 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319203, d367644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319203, d367644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319204 q = 1) (hb : d367645 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319204, d367645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319204, d367645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105144 (p : Pattern) (ha : d319210 p = 1) (hb : d367651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319205 q = 1) (hb : d367646 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319205, d367646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319205, d367646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105143 q ha hb
  have h2 (q : Pattern) (ha : d319206 q = 1) (hb : d367647 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319206, d367647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319206, d367647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319207 q = 1) (hb : d367648 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319207, d367648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319207, d367648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319208 q = 1) (hb : d367649 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319208, d367649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319208, d367649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319209 q = 1) (hb : d367650 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319209, d367650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319209, d367650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319210 q = 1) (hb : d367651 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319210, d367651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319210, d367651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105145 (p : Pattern) (ha : d45537 p = 1) (hb : d319354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45532 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
    | true =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
  have h5 (q : Pattern) (ha : d45533 q = 1) (hb : d319344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d319344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45533, d319344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45534 q = 1) (hb : d319351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d319351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45534, d319351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45535 q = 1) (hb : d319352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d319352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45535, d319352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45536 q = 1) (hb : d319353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d319353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45536, d319353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45537 q = 1) (hb : d319354 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45537, d319354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45537, d319354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105146 (p : Pattern) (ha : d45547 p = 1) (hb : d319375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319273 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45532 q = 1) (hb : d319247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105017 q ha hb
    | true =>
      simp only [d45532, d319247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105018 q ha hb
  have h4 (q : Pattern) (ha : d45533 q = 1) (hb : d319344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d319344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45533, d319344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45534 q = 1) (hb : d319351 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d319351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45534, d319351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45535 q = 1) (hb : d319352 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d319352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45535, d319352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45536 q = 1) (hb : d319353 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d319353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45536, d319353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319360 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319365 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d45542 q = 1) (hb : d319257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105020 q ha hb
    | true =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105021 q ha hb
  have h13 (q : Pattern) (ha : d45543 q = 1) (hb : d319368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d319368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45543, d319368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d45544 q = 1) (hb : d319372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d319372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45544, d319372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45545 q = 1) (hb : d319373 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d319373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45545, d319373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45546 q = 1) (hb : d319374 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d319374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45546, d319374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45547 q = 1) (hb : d319375 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45547, d319375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45547, d319375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105147 (p : Pattern) (ha : d319395 p = 1) (hb : d367655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45542 q = 1) (hb : d319257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105020 q ha hb
    | true =>
      simp only [d45542, d319257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105021 q ha hb
  have h3 (q : Pattern) (ha : d45543 q = 1) (hb : d319368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d319368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45543, d319368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319371 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45544 q = 1) (hb : d319372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d319372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45544, d319372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45545 q = 1) (hb : d319393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d319393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d319393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45546 q = 1) (hb : d319394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d319394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d319394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319395 q = 1) (hb : d367655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319395, d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319395, d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105148 (p : Pattern) (ha : d319480 p = 1) (hb : d367666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319469 q = 1) (hb : d367661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319469, d367661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105058 q hb ha
    | true =>
      simp only [d319469, d367661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105029 q hb ha
  have h3 (q : Pattern) (ha : d319470 q = 1) (hb : d367662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319470, d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319470, d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319477 q = 1) (hb : d367663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319477, d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319477, d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319478 q = 1) (hb : d367664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319478, d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319478, d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319479 q = 1) (hb : d367665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319479, d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319479, d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319480 q = 1) (hb : d367666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319480, d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319480, d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105149 (p : Pattern) (ha : d319493 p = 1) (hb : d367672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45548 q = 1) (hb : d319376 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d319376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105145 q ha hb
    | true =>
      simp only [d45548, d319376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105146 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45549 q = 1) (hb : d319390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d319390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d319390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319391 q = 1) (hb : d367653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319391, d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319391, d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319392 q = 1) (hb : d367654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319392, d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319392, d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319396 q = 1) (hb : d367656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319396, d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319396, d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105147 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319398 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319399 q = 1) (hb : d367657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319399, d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319399, d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319400 q = 1) (hb : d367658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319400, d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319400, d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319401 q = 1) (hb : d367659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319401, d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319401, d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319402 q = 1) (hb : d367660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319402, d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319402, d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319481 q = 1) (hb : d367667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319481, d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319481, d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105148 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319489 q = 1) (hb : d367668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319489, d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319489, d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319490 q = 1) (hb : d367669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319490, d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319490, d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319491 q = 1) (hb : d367670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319491, d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319491, d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319492 q = 1) (hb : d367671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319492, d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319492, d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319493 q = 1) (hb : d367672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319493, d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319493, d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105150 (p : Pattern) (ha : d319499 p = 1) (hb : d367678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319494 q = 1) (hb : d367673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319494, d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319494, d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105149 q ha hb
  have h2 (q : Pattern) (ha : d319495 q = 1) (hb : d367674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319495, d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319495, d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319496 q = 1) (hb : d367675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319496, d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319496, d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319497 q = 1) (hb : d367676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319497, d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319497, d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319498 q = 1) (hb : d367677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319498, d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319498, d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319499 q = 1) (hb : d367678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319499, d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319499, d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105151 (p : Pattern) (ha : d46001 p = 1) (hb : d319705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45996 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
    | true =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
  have h5 (q : Pattern) (ha : d45997 q = 1) (hb : d319686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d319686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45997, d319686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45998 q = 1) (hb : d319702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d319702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45998, d319702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45999 q = 1) (hb : d319703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d319703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45999, d319703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46000 q = 1) (hb : d319704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d319704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46000, d319704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46001 q = 1) (hb : d319705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46001, d319705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46001, d319705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105152 (p : Pattern) (ha : d46011 p = 1) (hb : d319726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319619 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45996 q = 1) (hb : d319593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105074 q ha hb
    | true =>
      simp only [d45996, d319593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105075 q ha hb
  have h4 (q : Pattern) (ha : d45997 q = 1) (hb : d319686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d319686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45997, d319686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d319701 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45998 q = 1) (hb : d319702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d319702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45998, d319702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45999 q = 1) (hb : d319703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d319703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45999, d319703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46000 q = 1) (hb : d319704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d319704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46000, d319704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d319711 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d319716 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46006 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105077 q ha hb
    | true =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105078 q ha hb
  have h13 (q : Pattern) (ha : d46007 q = 1) (hb : d319719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d319719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46007, d319719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46008 q = 1) (hb : d319723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d319723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46008, d319723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46009 q = 1) (hb : d319724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d319724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46009, d319724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46010 q = 1) (hb : d319725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d319725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46010, d319725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46011 q = 1) (hb : d319726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46011, d319726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46011, d319726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105153 (p : Pattern) (ha : d319746 p = 1) (hb : d367683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319718 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46006 q = 1) (hb : d319603 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105077 q ha hb
    | true =>
      simp only [d46006, d319603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105078 q ha hb
  have h3 (q : Pattern) (ha : d46007 q = 1) (hb : d319719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d319719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46007, d319719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319722 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46008 q = 1) (hb : d319723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d319723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46008, d319723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46009 q = 1) (hb : d319744 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d319744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d319744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46010 q = 1) (hb : d319745 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d319745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d319745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319746 q = 1) (hb : d367683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319746, d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319746, d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105154 (p : Pattern) (ha : d319867 p = 1) (hb : d367694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319847 q = 1) (hb : d367689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d319847, d367689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105117 q hb ha
    | true =>
      simp only [d319847, d367689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105086 q hb ha
  have h3 (q : Pattern) (ha : d319848 q = 1) (hb : d367690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d319848, d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319848, d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319863 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319864 q = 1) (hb : d367691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d319864, d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319864, d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319865 q = 1) (hb : d367692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d319865, d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319865, d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319866 q = 1) (hb : d367693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d319866, d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319866, d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d319867 q = 1) (hb : d367694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d319867, d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319867, d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105155 (p : Pattern) (ha : d319880 p = 1) (hb : d367700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d319611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46012 q = 1) (hb : d319727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d319727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105151 q ha hb
    | true =>
      simp only [d46012, d319727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105152 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d319740 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46013 q = 1) (hb : d319741 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d319741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d319741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319742 q = 1) (hb : d367681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319742, d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d319742, d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d319743 q = 1) (hb : d367682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319743, d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319743, d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d319747 q = 1) (hb : d367684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319747, d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319747, d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105153 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d319749 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d319750 q = 1) (hb : d367685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319750, d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d319750, d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d319751 q = 1) (hb : d367686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319751, d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d319751, d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d319752 q = 1) (hb : d367687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319752, d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d319752, d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d319753 q = 1) (hb : d367688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319753, d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d319753, d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d319868 q = 1) (hb : d367695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d319868, d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d319868, d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105154 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d319875 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d319876 q = 1) (hb : d367696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d319876, d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d319876, d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d319877 q = 1) (hb : d367697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d319877, d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d319877, d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d319878 q = 1) (hb : d367698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d319878, d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d319878, d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d319879 q = 1) (hb : d367699 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d319879, d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d319879, d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d319880 q = 1) (hb : d367700 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d319880, d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d319880, d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105156 (p : Pattern) (ha : d319886 p = 1) (hb : d367706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319881 q = 1) (hb : d367701 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d319881, d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319881, d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105155 q ha hb
  have h2 (q : Pattern) (ha : d319882 q = 1) (hb : d367702 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d319882, d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319882, d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d319883 q = 1) (hb : d367703 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d319883, d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319883, d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319884 q = 1) (hb : d367704 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d319884, d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319884, d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d319885 q = 1) (hb : d367705 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d319885, d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319885, d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319886 q = 1) (hb : d367706 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d319886, d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d319886, d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105157 (p : Pattern) (ha : d320471 p = 1) (hb : d367712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105156 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86365 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d320466 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320466, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320466, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88967 q ha hb
  have h12 (q : Pattern) (ha : d320467 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320467, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320467, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d320468 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320468, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320468, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d320469 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320469, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320469, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d320470 q = 1) (hb : d367711 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d320470, d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d320470, d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d320471 q = 1) (hb : d367712 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d320471, d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d320471, d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro105158 (p : Pattern) (ha : d320477 p = 1) (hb : d367718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320472 q = 1) (hb : d367713 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d320472, d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105157 q ha hb
    | true =>
      simp only [d320472, d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320473 q = 1) (hb : d367714 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d320473, d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320473, d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320474 q = 1) (hb : d367715 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d320474, d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320474, d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320475 q = 1) (hb : d367716 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d320475, d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320475, d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320476 q = 1) (hb : d367717 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d320476, d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320476, d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320477 q = 1) (hb : d367718 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d320477, d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320477, d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105159 (p : Pattern) (ha : d320483 p = 1) (hb : d367724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320478 q = 1) (hb : d367719 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d320478, d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105158 q ha hb
    | true =>
      simp only [d320478, d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320479 q = 1) (hb : d367720 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d320479, d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320479, d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320480 q = 1) (hb : d367721 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d320480, d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320480, d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320481 q = 1) (hb : d367722 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d320481, d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320481, d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320482 q = 1) (hb : d367723 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d320482, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320482, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320483 q = 1) (hb : d367724 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d320483, d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320483, d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105160 (p : Pattern) (ha : d320489 p = 1) (hb : d367730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320484 q = 1) (hb : d367725 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d320484, d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105159 q ha hb
    | true =>
      simp only [d320484, d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320485 q = 1) (hb : d367726 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d320485, d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320485, d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320486 q = 1) (hb : d367727 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d320486, d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320486, d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320487 q = 1) (hb : d367728 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d320487, d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320487, d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320488 q = 1) (hb : d367729 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d320488, d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320488, d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320489 q = 1) (hb : d367730 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d320489, d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320489, d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105161 (p : Pattern) (ha : d320495 p = 1) (hb : d367736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320490 q = 1) (hb : d367731 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d320490, d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105160 q ha hb
    | true =>
      simp only [d320490, d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320491 q = 1) (hb : d367732 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d320491, d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320491, d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320492 q = 1) (hb : d367733 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d320492, d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320492, d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320493 q = 1) (hb : d367734 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d320493, d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320493, d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320494 q = 1) (hb : d367735 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d320494, d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320494, d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320495 q = 1) (hb : d367736 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d320495, d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320495, d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105162 (p : Pattern) (ha : d320501 p = 1) (hb : d367742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320496 q = 1) (hb : d367737 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d320496, d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105161 q ha hb
    | true =>
      simp only [d320496, d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320497 q = 1) (hb : d367738 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d320497, d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320497, d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320498 q = 1) (hb : d367739 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d320498, d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320498, d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320499 q = 1) (hb : d367740 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d320499, d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320499, d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320500 q = 1) (hb : d367741 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d320500, d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320500, d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320501 q = 1) (hb : d367742 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d320501, d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320501, d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105163 (p : Pattern) (ha : d320507 p = 1) (hb : d367748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320502 q = 1) (hb : d367743 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d320502, d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105162 q ha hb
    | true =>
      simp only [d320502, d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320503 q = 1) (hb : d367744 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d320503, d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320503, d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320504 q = 1) (hb : d367745 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d320504, d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320504, d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320505 q = 1) (hb : d367746 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d320505, d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320505, d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320506 q = 1) (hb : d367747 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d320506, d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320506, d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320507 q = 1) (hb : d367748 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d320507, d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320507, d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105164 (p : Pattern) (ha : d320513 p = 1) (hb : d367754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320508 q = 1) (hb : d367749 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d320508, d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105163 q ha hb
    | true =>
      simp only [d320508, d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d320509 q = 1) (hb : d367750 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d320509, d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320509, d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d320510 q = 1) (hb : d367751 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d320510, d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320510, d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d320511 q = 1) (hb : d367752 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d320511, d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320511, d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d320512 q = 1) (hb : d367753 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d320512, d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d320512, d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d320513 q = 1) (hb : d367754 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d320513, d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320513, d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105165 (p : Pattern) (ha : d44973 p = 1) (hb : d322048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44909 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44969 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44969, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44970 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44970, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44971 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44971, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44972 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44972, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44973 q = 1) (hb : d322048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44973, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44973, d322048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105166 (p : Pattern) (ha : d44980 p = 1) (hb : d322053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44909 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44969 q = 1) (hb : d322044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44969, d322044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45067 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44970 q = 1) (hb : d322045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44970, d322045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44971 q = 1) (hb : d322046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44971, d322046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44972 q = 1) (hb : d322047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d322047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45076 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45080 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d44916 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44976 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44976, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44977 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44977, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44978 q = 1) (hb : d322051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44978, d322051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44979 q = 1) (hb : d322052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44979, d322052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44980 q = 1) (hb : d322053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44980, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44980, d322053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105167 (p : Pattern) (ha : d322060 p = 1) (hb : d367603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44976 q = 1) (hb : d322049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44976, d322049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45088 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44977 q = 1) (hb : d322050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44977, d322050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44978 q = 1) (hb : d322058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d322058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44979 q = 1) (hb : d322059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d322059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322060 q = 1) (hb : d367603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322060, d367603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322060, d367603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105168 (p : Pattern) (ha : d322070 p = 1) (hb : d367613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44952 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322066 q = 1) (hb : d367609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322066, d367609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322066, d367609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322067 q = 1) (hb : d367610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322067, d367610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322067, d367610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322068 q = 1) (hb : d367611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322068, d367611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322068, d367611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322069 q = 1) (hb : d367612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322069, d367612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322069, d367612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322070 q = 1) (hb : d367613 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322070, d367613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322070, d367613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105169 (p : Pattern) (ha : d322076 p = 1) (hb : d367619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44981 q = 1) (hb : d322054 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105165 q ha hb
    | true =>
      simp only [d44981, d322054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105166 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44982 q = 1) (hb : d322055 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d322055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322056 q = 1) (hb : d367601 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322056, d367601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322056, d367601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322057 q = 1) (hb : d367602 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322057, d367602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322057, d367602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322061 q = 1) (hb : d367604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322061, d367604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322061, d367604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105167 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322062 q = 1) (hb : d367605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322062, d367605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322062, d367605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322063 q = 1) (hb : d367606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322063, d367606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322063, d367606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322064 q = 1) (hb : d367607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322064, d367607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322064, d367607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322065 q = 1) (hb : d367608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322065, d367608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322065, d367608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322071 q = 1) (hb : d367614 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322071, d367614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322071, d367614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105168 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322072 q = 1) (hb : d367615 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322072, d367615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322072, d367615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322073 q = 1) (hb : d367616 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322073, d367616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322073, d367616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322074 q = 1) (hb : d367617 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322074, d367617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322074, d367617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322075 q = 1) (hb : d367618 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322075, d367618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322075, d367618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322076 q = 1) (hb : d367619 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322076, d367619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322076, d367619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105170 (p : Pattern) (ha : d322082 p = 1) (hb : d367625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86400 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322077 q = 1) (hb : d367620 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322077, d367620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322077, d367620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105169 q ha hb
  have h8 (q : Pattern) (ha : d322078 q = 1) (hb : d367621 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322078, d367621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322078, d367621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d322079 q = 1) (hb : d367622 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322079, d367622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322079, d367622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322080 q = 1) (hb : d367623 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322080, d367623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322080, d367623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d322081 q = 1) (hb : d367624 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322081, d367624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322081, d367624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d322082 q = 1) (hb : d367625 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d367625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d322082, d367625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro105171 (p : Pattern) (ha : d45195 p = 1) (hb : d322087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45190 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45191 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45191, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45192 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45192, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45193 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45193, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45194 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45194, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45195 q = 1) (hb : d322087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45195, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45195, d322087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105172 (p : Pattern) (ha : d45205 p = 1) (hb : d322092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45216 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45190 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45191 q = 1) (hb : d322083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45191, d322083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45192 q = 1) (hb : d322084 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45192, d322084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45193 q = 1) (hb : d322085 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45193, d322085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45194 q = 1) (hb : d322086 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d322086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d45200 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d45201 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45201, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d45202 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45202, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45203 q = 1) (hb : d322090 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45203, d322090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45204 q = 1) (hb : d322091 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45204, d322091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45205 q = 1) (hb : d322092 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45205, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45205, d322092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105173 (p : Pattern) (ha : d322099 p = 1) (hb : d367628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45345 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45201 q = 1) (hb : d322088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45201, d322088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45352 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45202 q = 1) (hb : d322089 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45202, d322089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45203 q = 1) (hb : d322097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d322097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45204 q = 1) (hb : d322098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d322098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322099 q = 1) (hb : d367628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322099, d367628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322099, d367628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105174 (p : Pattern) (ha : d322109 p = 1) (hb : d367639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d367634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322105 q = 1) (hb : d367635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322105, d367635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322105, d367635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45468 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322106 q = 1) (hb : d367636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322106, d367636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322106, d367636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322107 q = 1) (hb : d367637 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322107, d367637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322107, d367637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322108 q = 1) (hb : d367638 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322108, d367638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322108, d367638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322109 q = 1) (hb : d367639 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322109, d367639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322109, d367639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105175 (p : Pattern) (ha : d322115 p = 1) (hb : d367645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45208 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45206 q = 1) (hb : d322093 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105171 q ha hb
    | true =>
      simp only [d45206, d322093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105172 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45370 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45207 q = 1) (hb : d322094 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d322094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322095 q = 1) (hb : d367626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322095, d367626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322095, d367626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322096 q = 1) (hb : d367627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322096, d367627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322096, d367627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322100 q = 1) (hb : d367629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322100, d367629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322100, d367629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105173 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d45379 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322101 q = 1) (hb : d367630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322101, d367630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322101, d367630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322102 q = 1) (hb : d367631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322102, d367631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322102, d367631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322103 q = 1) (hb : d367632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322103, d367632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322103, d367632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322104 q = 1) (hb : d367633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322104, d367633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322104, d367633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322110 q = 1) (hb : d367640 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322110, d367640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322110, d367640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105174 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45484 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322111 q = 1) (hb : d367641 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322111, d367641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322111, d367641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322112 q = 1) (hb : d367642 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322112, d367642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322112, d367642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322113 q = 1) (hb : d367643 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322113, d367643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322113, d367643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322114 q = 1) (hb : d367644 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322114, d367644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322114, d367644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322115 q = 1) (hb : d367645 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322115, d367645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322115, d367645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105176 (p : Pattern) (ha : d322121 p = 1) (hb : d367651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322116 q = 1) (hb : d367646 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322116, d367646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322116, d367646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105175 q ha hb
  have h2 (q : Pattern) (ha : d322117 q = 1) (hb : d367647 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322117, d367647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322117, d367647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322118 q = 1) (hb : d367648 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322118, d367648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322118, d367648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322119 q = 1) (hb : d367649 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322119, d367649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322119, d367649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322120 q = 1) (hb : d367650 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322120, d367650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322120, d367650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322121 q = 1) (hb : d367651 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322121, d367651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322121, d367651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105177 (p : Pattern) (ha : d45537 p = 1) (hb : d322127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45532 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45533 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45533, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45534 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45534, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45535 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45535, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45536 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45536, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45537 q = 1) (hb : d322127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45537, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45537, d322127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105178 (p : Pattern) (ha : d45547 p = 1) (hb : d322132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45532 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45533 q = 1) (hb : d322123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45533, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45533, d322123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d45703 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45534 q = 1) (hb : d322124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45534, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45534, d322124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45535 q = 1) (hb : d322125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45535, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45535, d322125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45536 q = 1) (hb : d322126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45536, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45536, d322126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d45713 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d45718 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d45542 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d45543 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45543, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d45544 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45544, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45545 q = 1) (hb : d322130 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45545, d322130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45546 q = 1) (hb : d322131 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45546, d322131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45547 q = 1) (hb : d322132 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45547, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45547, d322132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105179 (p : Pattern) (ha : d322139 p = 1) (hb : d367655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45720 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45542 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45543 q = 1) (hb : d322128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45543, d322128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45544 q = 1) (hb : d322129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45544, d322129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45545 q = 1) (hb : d322137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d322137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45546 q = 1) (hb : d322138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d322138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322139 q = 1) (hb : d367655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322139, d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322139, d367655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105180 (p : Pattern) (ha : d322149 p = 1) (hb : d367666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d367661 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322145 q = 1) (hb : d367662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322145, d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322145, d367662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45875 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322146 q = 1) (hb : d367663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322146, d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322146, d367663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322147 q = 1) (hb : d367664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322147, d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322147, d367664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322148 q = 1) (hb : d367665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322148, d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322148, d367665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322149 q = 1) (hb : d367666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322149, d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322149, d367666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105181 (p : Pattern) (ha : d322155 p = 1) (hb : d367672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d45550 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45548 q = 1) (hb : d322133 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105177 q ha hb
    | true =>
      simp only [d45548, d322133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105178 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d45745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45549 q = 1) (hb : d322134 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d322134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322135 q = 1) (hb : d367653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322135, d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322135, d367653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322136 q = 1) (hb : d367654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322136, d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322136, d367654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322140 q = 1) (hb : d367656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322140, d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322140, d367656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105179 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d45754 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322141 q = 1) (hb : d367657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322141, d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322141, d367657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322142 q = 1) (hb : d367658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322142, d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322142, d367658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322143 q = 1) (hb : d367659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322143, d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322143, d367659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322144 q = 1) (hb : d367660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322144, d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322144, d367660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322150 q = 1) (hb : d367667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322150, d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322150, d367667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105180 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d45891 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322151 q = 1) (hb : d367668 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322151, d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322151, d367668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322152 q = 1) (hb : d367669 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322152, d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322152, d367669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322153 q = 1) (hb : d367670 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322153, d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322153, d367670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322154 q = 1) (hb : d367671 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322154, d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322154, d367671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322155 q = 1) (hb : d367672 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322155, d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322155, d367672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105182 (p : Pattern) (ha : d322161 p = 1) (hb : d367678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322156 q = 1) (hb : d367673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322156, d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322156, d367673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105181 q ha hb
  have h2 (q : Pattern) (ha : d322157 q = 1) (hb : d367674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322157, d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322157, d367674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322158 q = 1) (hb : d367675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322158, d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322158, d367675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322159 q = 1) (hb : d367676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322159, d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322159, d367676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322160 q = 1) (hb : d367677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322160, d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322160, d367677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322161 q = 1) (hb : d367678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322161, d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322161, d367678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105183 (p : Pattern) (ha : d46001 p = 1) (hb : d322168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46088 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d45996 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45997 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45997, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d45998 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45998, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45999 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45999, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46000 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46000, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46001 q = 1) (hb : d322168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46001, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46001, d322168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105184 (p : Pattern) (ha : d46011 p = 1) (hb : d322173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46022 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46088 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d45996 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d45997 q = 1) (hb : d322164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45997, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45997, d322164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d46211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45998 q = 1) (hb : d322165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45998, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45998, d322165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45999 q = 1) (hb : d322166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45999, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45999, d322166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46000 q = 1) (hb : d322167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46000, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46000, d322167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d46221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d46226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d46228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46006 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46007 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46007, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46008 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46008, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46009 q = 1) (hb : d322171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46009, d322171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46010 q = 1) (hb : d322172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46010, d322172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46011 q = 1) (hb : d322173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46011, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46011, d322173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105185 (p : Pattern) (ha : d322180 p = 1) (hb : d367683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46007 q = 1) (hb : d322169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46007, d322169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46008 q = 1) (hb : d322170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46008, d322170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46009 q = 1) (hb : d322178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d322178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46010 q = 1) (hb : d322179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d322179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322180 q = 1) (hb : d367683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322180, d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322180, d367683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105186 (p : Pattern) (ha : d322190 p = 1) (hb : d367694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d367689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d322186 q = 1) (hb : d367690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322186, d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322186, d367690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46428 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322187 q = 1) (hb : d367691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322187, d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322187, d367691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d322188 q = 1) (hb : d367692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322188, d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322188, d367692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322189 q = 1) (hb : d367693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322189, d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322189, d367693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322190 q = 1) (hb : d367694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322190, d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322190, d367694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105187 (p : Pattern) (ha : d322196 p = 1) (hb : d367700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46012 q = 1) (hb : d322174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105183 q ha hb
    | true =>
      simp only [d46012, d322174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105184 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46013 q = 1) (hb : d322175 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d322175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322176 q = 1) (hb : d367681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322176, d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322176, d367681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322177 q = 1) (hb : d367682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322177, d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322177, d367682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d322181 q = 1) (hb : d367684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322181, d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322181, d367684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105185 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d46262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d322182 q = 1) (hb : d367685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322182, d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322182, d367685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d322183 q = 1) (hb : d367686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322183, d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322183, d367686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d322184 q = 1) (hb : d367687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322184, d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322184, d367687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d322185 q = 1) (hb : d367688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322185, d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322185, d367688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d322191 q = 1) (hb : d367695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322191, d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322191, d367695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105186 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d46444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d322192 q = 1) (hb : d367696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322192, d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322192, d367696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d322193 q = 1) (hb : d367697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322193, d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322193, d367697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d322194 q = 1) (hb : d367698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322194, d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322194, d367698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d322195 q = 1) (hb : d367699 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322195, d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322195, d367699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d322196 q = 1) (hb : d367700 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322196, d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322196, d367700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105188 (p : Pattern) (ha : d322202 p = 1) (hb : d367706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322197 q = 1) (hb : d367701 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322197, d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322197, d367701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105187 q ha hb
  have h2 (q : Pattern) (ha : d322198 q = 1) (hb : d367702 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322198, d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322198, d367702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d322199 q = 1) (hb : d367703 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322199, d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322199, d367703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322200 q = 1) (hb : d367704 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322200, d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322200, d367704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322201 q = 1) (hb : d367705 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322201, d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322201, d367705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322202 q = 1) (hb : d367706 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322202, d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322202, d367706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105189 (p : Pattern) (ha : d322208 p = 1) (hb : d367712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322203 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105188 q ha hb
  have h5 (q : Pattern) (ha : d322204 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322205 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321678 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86389 q ha hb
  have h8 (q : Pattern) (ha : d321679 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321680 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322206 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d321721 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321721, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321721, d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88984 q ha hb
  have h12 (q : Pattern) (ha : d321722 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321722, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321722, d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d321723 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321723, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321723, d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d321724 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d321724, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321724, d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d322207 q = 1) (hb : d367711 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d322207, d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322207, d367711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d322208 q = 1) (hb : d367712 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d322208, d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322208, d367712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro105190 (p : Pattern) (ha : d322214 p = 1) (hb : d367718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322209 q = 1) (hb : d367713 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d322209, d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105189 q ha hb
    | true =>
      simp only [d322209, d367713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322210 q = 1) (hb : d367714 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d322210, d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322210, d367714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322211 q = 1) (hb : d367715 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d322211, d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322211, d367715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322212 q = 1) (hb : d367716 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d322212, d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322212, d367716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322213 q = 1) (hb : d367717 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d322213, d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322213, d367717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322214 q = 1) (hb : d367718 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d322214, d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322214, d367718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105191 (p : Pattern) (ha : d322220 p = 1) (hb : d367724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322215 q = 1) (hb : d367719 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d322215, d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105190 q ha hb
    | true =>
      simp only [d322215, d367719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322216 q = 1) (hb : d367720 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d322216, d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322216, d367720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322217 q = 1) (hb : d367721 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d322217, d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322217, d367721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322218 q = 1) (hb : d367722 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322218, d367722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322219 q = 1) (hb : d367723 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322219, d367723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322220 q = 1) (hb : d367724 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322220, d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105192 (p : Pattern) (ha : d322226 p = 1) (hb : d367730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d367725 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105191 q ha hb
    | true =>
      simp only [d322221, d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d367726 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d367727 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d367728 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d367729 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d367730 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105193 (p : Pattern) (ha : d322232 p = 1) (hb : d367736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d367731 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105192 q ha hb
    | true =>
      simp only [d322227, d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d367732 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d367733 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d367734 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d367735 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d367736 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105194 (p : Pattern) (ha : d322238 p = 1) (hb : d367742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d367737 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105193 q ha hb
    | true =>
      simp only [d322233, d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d367738 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d367739 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d367740 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d367741 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d367742 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105195 (p : Pattern) (ha : d322244 p = 1) (hb : d367748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d367743 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105194 q ha hb
    | true =>
      simp only [d322239, d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d367744 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d367745 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d367746 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d367747 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d367748 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105196 (p : Pattern) (ha : d322250 p = 1) (hb : d367754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d367749 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105195 q ha hb
    | true =>
      simp only [d322245, d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d367750 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d367751 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d367752 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d367753 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d367754 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105197 (p : Pattern) (ha : d322220 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370806 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322219 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d370807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322219, d370807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322220 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro105198 (p : Pattern) (ha : d322226 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105197 q ha hb
    | true =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105199 (p : Pattern) (ha : d322232 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105198 q ha hb
    | true =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105200 (p : Pattern) (ha : d322238 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105199 q ha hb
    | true =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105201 (p : Pattern) (ha : d322244 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105200 q ha hb
    | true =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105202 (p : Pattern) (ha : d322250 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105201 q ha hb
    | true =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105203 (p : Pattern) (ha : d0 p = 1) (hb : d370891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370891 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro105204 (p : Pattern) (ha : d367724 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d367722 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370806 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d367723 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d370807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367723, d370807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d367724 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro105205 (p : Pattern) (ha : d367730 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367725 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105204 q ha hb
    | true =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367726 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367727 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367728 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367729 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367730 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105206 (p : Pattern) (ha : d367736 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367731 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105205 q ha hb
    | true =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367732 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367733 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367734 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367735 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367736 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105207 (p : Pattern) (ha : d367742 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367737 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105206 q ha hb
    | true =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367738 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367739 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367740 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367741 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367742 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105208 (p : Pattern) (ha : d367748 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367743 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105207 q ha hb
    | true =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367744 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367745 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367746 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367747 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367748 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105209 (p : Pattern) (ha : d367754 p = 1) (hb : d370807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367749 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105208 q ha hb
    | true =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367750 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367751 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367752 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367753 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367754 q = 1) (hb : d370807 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105210 (p : Pattern) (ha : d0 p = 1) (hb : d370933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370933 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro105211 (p : Pattern) (ha : d322220 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322219 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d370936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322219, d370936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322220 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro105212 (p : Pattern) (ha : d322226 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105211 q ha hb
    | true =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105213 (p : Pattern) (ha : d322232 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105212 q ha hb
    | true =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105214 (p : Pattern) (ha : d322238 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105213 q ha hb
    | true =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105215 (p : Pattern) (ha : d322244 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105214 q ha hb
    | true =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105216 (p : Pattern) (ha : d322250 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105215 q ha hb
    | true =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105217 (p : Pattern) (ha : d367724 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d367722 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d370935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d367723 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d370936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367723, d370936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d367724 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro105218 (p : Pattern) (ha : d367730 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367725 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105217 q ha hb
    | true =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367726 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367727 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367728 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367729 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367730 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105219 (p : Pattern) (ha : d367736 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367731 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105218 q ha hb
    | true =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367732 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367733 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367734 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367735 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367736 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105220 (p : Pattern) (ha : d367742 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367737 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105219 q ha hb
    | true =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367738 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367739 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367740 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367741 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367742 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105221 (p : Pattern) (ha : d367748 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367743 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105220 q ha hb
    | true =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367744 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367745 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367746 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367747 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367748 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105222 (p : Pattern) (ha : d367754 p = 1) (hb : d370936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367749 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105221 q ha hb
    | true =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367750 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367751 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367752 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367753 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367754 q = 1) (hb : d370936 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105223 (p : Pattern) (ha : d14 p = 1) (hb : d46867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46865 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46866 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46867 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h6 p ha hb
theorem andIntro105224 (p : Pattern) (ha : d14 p = 1) (hb : d46876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46868 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46869 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46876 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105225 (p : Pattern) (ha : d14 p = 1) (hb : d46882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46882 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105226 (p : Pattern) (ha : d14 p = 1) (hb : d46884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46884 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105227 (p : Pattern) (ha : d14 p = 1) (hb : d46888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46868 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46869 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46888 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro105228 (p : Pattern) (ha : d14 p = 1) (hb : d46894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46889 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105227 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46890 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46891 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46892 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d46893 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d46894 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105229 (p : Pattern) (ha : d14 p = 1) (hb : d46901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105225 q ha hb
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105226 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105226 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105228 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46900 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d46901 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro105230 (p : Pattern) (ha : d14 p = 1) (hb : d46905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105226 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105228 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105231 (p : Pattern) (ha : d14 p = 1) (hb : d46911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105229 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105232 (p : Pattern) (ha : d14 p = 1) (hb : d46915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105233 (p : Pattern) (ha : d14 p = 1) (hb : d46921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105231 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105232 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105234 (p : Pattern) (ha : d14 p = 1) (hb : d46924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105229 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro105235 (p : Pattern) (ha : d14 p = 1) (hb : d46925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105236 (p : Pattern) (ha : d14 p = 1) (hb : d46931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105231 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105232 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105234 q ha hb
    | true =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105235 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d46930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d46931 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105237 (p : Pattern) (ha : d14 p = 1) (hb : d47065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105231 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105232 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105232 q ha hb
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d47061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d47062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d47063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d47064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d47065 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105238 (p : Pattern) (ha : d14 p = 1) (hb : d47071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105232 q ha hb
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d47061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d47063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105235 q ha hb
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d47067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d47068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d47069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d47070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d47071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105239 (p : Pattern) (ha : d14 p = 1) (hb : d47080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105235 q ha hb
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d47067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d47069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105240 (p : Pattern) (ha : d14 p = 1) (hb : d47096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d47090 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d47095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d47096 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105241 (p : Pattern) (ha : d14 p = 1) (hb : d47106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d47095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d47101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105227 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46889 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105227 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d47102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d46890 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d47103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d47104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d47105 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d47106 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105242 (p : Pattern) (ha : d14 p = 1) (hb : d47125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47107 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105240 q ha hb
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105241 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d47108 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47109 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d47115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47124 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105243 (p : Pattern) (ha : d14 p = 1) (hb : d47216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105242 q ha hb
    | true =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d47127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d47214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105244 (p : Pattern) (ha : d14 p = 1) (hb : d47222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105243 q ha hb
    | true =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d47218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d47220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105245 (p : Pattern) (ha : d14 p = 1) (hb : d46936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105229 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105246 (p : Pattern) (ha : d14 p = 1) (hb : d46938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46937 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46938 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105247 (p : Pattern) (ha : d14 p = 1) (hb : d46945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105229 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105248 (p : Pattern) (ha : d14 p = 1) (hb : d46948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105230 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105249 (p : Pattern) (ha : d14 p = 1) (hb : d46957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105225 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105225 q ha hb
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105226 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d46955 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105226 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105228 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d46898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d46956 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d46957 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
end NetHack.Soko22Hazard87
