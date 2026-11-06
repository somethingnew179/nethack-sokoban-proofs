import NetHack.Soko22Hazard87.AndIntroBlocks0161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro40500 (p : Pattern) (ha : d144528 p = 1) (hb : d160236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144514 q = 1) (hb : d160222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144514, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40498 q ha hb
    | true =>
      simp only [d144514, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144515 q = 1) (hb : d160223 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144515, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144515, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144516 q = 1) (hb : d160224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144516, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144516, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144517 q = 1) (hb : d160225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144517, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144517, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144518 q = 1) (hb : d160226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144518, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144518, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144528 q = 1) (hb : d160236 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144528, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144528, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40501 (p : Pattern) (ha : d52593 p = 1) (hb : d160248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
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
  have h8 (q : Pattern) (ha : d52593 q = 1) (hb : d160247 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52593 q = 1) (hb : d160248 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40502 (p : Pattern) (ha : d144559 p = 1) (hb : d160271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144541 q = 1) (hb : d160253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40501 q ha hb
    | true =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144542 q = 1) (hb : d160254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144543 q = 1) (hb : d160255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144549 q = 1) (hb : d160261 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144549, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144549, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144558 q = 1) (hb : d160270 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d144558, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144558, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144559 q = 1) (hb : d160271 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d144559, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144559, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40503 (p : Pattern) (ha : d144570 p = 1) (hb : d160294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144560 q = 1) (hb : d160272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144560, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40502 q ha hb
    | true =>
      simp only [d144560, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144561 q = 1) (hb : d160273 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144561, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144561, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144567 q = 1) (hb : d160291 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144567, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144567, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144568 q = 1) (hb : d160292 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144568, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144568, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144569 q = 1) (hb : d160293 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144569, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144569, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144570 q = 1) (hb : d160294 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144570, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144570, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40504 (p : Pattern) (ha : d144589 p = 1) (hb : d160300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144584 q = 1) (hb : d160295 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144584, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40503 q ha hb
    | true =>
      simp only [d144584, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144585 q = 1) (hb : d160296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144585, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144585, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144586 q = 1) (hb : d160297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144586, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144586, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144587 q = 1) (hb : d160298 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144587, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144587, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144588 q = 1) (hb : d160299 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144588, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144588, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144589 q = 1) (hb : d160300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d144589, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144589, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40505 (p : Pattern) (ha : d177377 p = 1) (hb : d178302 p = 1) : d179305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177372 q = 1) (hb : d178297 q = 1) : d179300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177372, d178297, d179300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40478 q ha hb
    | true =>
      simp only [d177372, d178297, d179300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40495 q ha hb
  have h2 (q : Pattern) (ha : d177373 q = 1) (hb : d178298 q = 1) : d179301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177373, d178298, d179301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177373, d178298, d179301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177374 q = 1) (hb : d178299 q = 1) : d179302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177374, d178299, d179302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177374, d178299, d179302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144405 q = 1) (hb : d160111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40495 q ha hb
    | true =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144406 q = 1) (hb : d160112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144407 q = 1) (hb : d160113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177375 q = 1) (hb : d178300 q = 1) : d179303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177375, d178300, d179303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177375, d178300, d179303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144409 q = 1) (hb : d160115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144409, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144409, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177376 q = 1) (hb : d178301 q = 1) : d179304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177376, d178301, d179304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177376, d178301, d179304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177377 q = 1) (hb : d178302 q = 1) : d179305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177377, d178302, d179305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d177377, d178302, d179305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro40506 (p : Pattern) (ha : d177383 p = 1) (hb : d178308 p = 1) : d179311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177381 q = 1) (hb : d178306 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177382 q = 1) (hb : d178307 q = 1) : d179310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177382, d178307, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177382, d178307, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177383 q = 1) (hb : d178308 q = 1) : d179311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177383, d178308, d179311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177383, d178308, d179311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40507 (p : Pattern) (ha : d177389 p = 1) (hb : d178314 p = 1) : d179317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177384 q = 1) (hb : d178309 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
    | true =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
  have h2 (q : Pattern) (ha : d177385 q = 1) (hb : d178310 q = 1) : d179313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177386 q = 1) (hb : d178311 q = 1) : d179314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177387 q = 1) (hb : d178312 q = 1) : d179315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177388 q = 1) (hb : d178313 q = 1) : d179316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177389 q = 1) (hb : d178314 q = 1) : d179317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177389, d178314, d179317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177389, d178314, d179317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40508 (p : Pattern) (ha : d177392 p = 1) (hb : d178317 p = 1) : d179320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177381 q = 1) (hb : d178306 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177382 q = 1) (hb : d178307 q = 1) : d179310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177382, d178307, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177382, d178307, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177392 q = 1) (hb : d178317 q = 1) : d179320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177392, d178317, d179320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177392, d178317, d179320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40509 (p : Pattern) (ha : d177398 p = 1) (hb : d178323 p = 1) : d179326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177384 q = 1) (hb : d178309 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
    | true =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
  have h2 (q : Pattern) (ha : d177385 q = 1) (hb : d178310 q = 1) : d179313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177386 q = 1) (hb : d178311 q = 1) : d179314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177387 q = 1) (hb : d178312 q = 1) : d179315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177388 q = 1) (hb : d178313 q = 1) : d179316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177393 q = 1) (hb : d178318 q = 1) : d179321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40508 q ha hb
    | true =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40498 q ha hb
  have h7 (q : Pattern) (ha : d177394 q = 1) (hb : d178319 q = 1) : d179322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177394, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177394, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177395 q = 1) (hb : d178320 q = 1) : d179323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177395, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177395, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177396 q = 1) (hb : d178321 q = 1) : d179324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177396, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177396, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177397 q = 1) (hb : d178322 q = 1) : d179325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177397, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177397, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177398 q = 1) (hb : d178323 q = 1) : d179326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177398, d178323, d179326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177398, d178323, d179326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40510 (p : Pattern) (ha : d144448 p = 1) (hb : d160154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144423 q = 1) (hb : d160129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144447 q = 1) (hb : d160153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144447, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144447, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144448 q = 1) (hb : d160154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144448, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144448, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40511 (p : Pattern) (ha : d144458 p = 1) (hb : d160164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144456 q = 1) (hb : d160162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144456, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144456, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144457 q = 1) (hb : d160163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144457, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144457, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144458 q = 1) (hb : d160164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144458, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144458, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40512 (p : Pattern) (ha : d177403 p = 1) (hb : d178328 p = 1) : d179331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177381 q = 1) (hb : d178306 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177402 q = 1) (hb : d178327 q = 1) : d179330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177402, d178327, d179330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177402, d178327, d179330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177403 q = 1) (hb : d178328 q = 1) : d179331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177403, d178328, d179331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177403, d178328, d179331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40513 (p : Pattern) (ha : d177410 p = 1) (hb : d178335 p = 1) : d179338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177408 q = 1) (hb : d178333 q = 1) : d179336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177408, d178333, d179336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177408, d178333, d179336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177409 q = 1) (hb : d178334 q = 1) : d179337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177409, d178334, d179337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177409, d178334, d179337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177410 q = 1) (hb : d178335 q = 1) : d179338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177410, d178335, d179338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177410, d178335, d179338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40514 (p : Pattern) (ha : d312 p = 1) (hb : d101160 p = 1) : d179345 p = 1 := by
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
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d310 q = 1) (hb : d52502 q = 1) : d179342 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d52502, d179342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310, d52502, d179342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d130 q = 1) : d130 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d311 q = 1) (hb : d69208 q = 1) : d179343 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d69208, d179343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d311, d69208, d179343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d13 q = 1) : d13 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d128 q = 1) (hb : d52107 q = 1) : d44880 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128, d52107, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d129 q = 1) (hb : d52960 q = 1) : d44881 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d52960, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129, d52960, d44881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d15 q = 1) : d15 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d130 q = 1) (hb : d52972 q = 1) : d44882 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d52972, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130, d52972, d44882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
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
  have h18 (q : Pattern) (ha : d131 q = 1) (hb : d101159 q = 1) : d179344 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d101159, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d131, d101159, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d312 q = 1) (hb : d101160 q = 1) : d179345 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d101160, d179345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d312, d101160, d179345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40515 (p : Pattern) (ha : d9586 p = 1) (hb : d101176 p = 1) : d179351 p = 1 := by
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
  have h3 (q : Pattern) (ha : d313 q = 1) (hb : d101161 q = 1) : d179346 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d101161, d179346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40514 q ha hb
    | true =>
      simp only [d313, d101161, d179346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d314 q = 1) (hb : d101162 q = 1) : d179347 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d101162, d179347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d314, d101162, d179347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d533 q = 1) (hb : d101173 q = 1) : d179348 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d101173, d179348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d533, d101173, d179348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d539 q = 1) : d539 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d540 q = 1) (hb : d101174 q = 1) : d179349 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d101174, d179349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d540, d101174, d179349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d541 q = 1) (hb : d101175 q = 1) : d179350 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d101175, d179350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d541, d101175, d179350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9581 q = 1) (hb : d101161 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9582 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9583 q = 1) (hb : d101163 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d101163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9583, d101163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9584 q = 1) (hb : d101164 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d101164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9584, d101164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9585 q = 1) (hb : d101165 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d101165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9585, d101165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9586 q = 1) (hb : d101176 q = 1) : d179351 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9586, d101176, d179351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9586, d101176, d179351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40516 (p : Pattern) (ha : d122767 p = 1) (hb : d178340 p = 1) : d179357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9587 q = 1) (hb : d101177 q = 1) : d179352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101177, d179352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40515 q ha hb
    | true =>
      simp only [d9587, d101177, d179352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9589 q = 1) (hb : d101179 q = 1) : d179353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101179, d179353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9589, d101179, d179353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16270 q = 1) (hb : d122766 q = 1) : d179354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d122766, d179354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16270, d122766, d179354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16271 q = 1) (hb : d122767 q = 1) : d179355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d122767, d179355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16271, d122767, d179355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d122767 q = 1) (hb : d178339 q = 1) : d179356 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178339, d179356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178339, d179356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122767 q = 1) (hb : d178340 q = 1) : d179357 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178340, d179357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178340, d179357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40517 (p : Pattern) (ha : d177419 p = 1) (hb : d178346 p = 1) : d179363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177414 q = 1) (hb : d178341 q = 1) : d179358 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177414, d178341, d179358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40516 q ha hb
    | true =>
      simp only [d177414, d178341, d179358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40478 q ha hb
  have h2 (q : Pattern) (ha : d177415 q = 1) (hb : d178342 q = 1) : d179359 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177415, d178342, d179359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177415, d178342, d179359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177416 q = 1) (hb : d178343 q = 1) : d179360 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177416, d178343, d179360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177416, d178343, d179360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177372 q = 1) (hb : d178297 q = 1) : d179300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177372, d178297, d179300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40478 q ha hb
    | true =>
      simp only [d177372, d178297, d179300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40495 q ha hb
  have h5 (q : Pattern) (ha : d177373 q = 1) (hb : d178298 q = 1) : d179301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177373, d178298, d179301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177373, d178298, d179301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177374 q = 1) (hb : d178299 q = 1) : d179302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177374, d178299, d179302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177374, d178299, d179302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177417 q = 1) (hb : d178344 q = 1) : d179361 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177417, d178344, d179361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177417, d178344, d179361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144405 q = 1) (hb : d160111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40495 q ha hb
    | true =>
      simp only [d144405, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144406 q = 1) (hb : d160112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144406, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144407 q = 1) (hb : d160113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144407, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177375 q = 1) (hb : d178300 q = 1) : d179303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177375, d178300, d179303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177375, d178300, d179303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d177418 q = 1) (hb : d178345 q = 1) : d179362 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177418, d178345, d179362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177418, d178345, d179362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d177419 q = 1) (hb : d178346 q = 1) : d179363 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177419, d178346, d179363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177419, d178346, d179363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40518 (p : Pattern) (ha : d177425 p = 1) (hb : d178352 p = 1) : d179369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177420 q = 1) (hb : d178347 q = 1) : d179364 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177420, d178347, d179364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40517 q ha hb
    | true =>
      simp only [d177420, d178347, d179364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177421 q = 1) (hb : d178348 q = 1) : d179365 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177421, d178348, d179365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177421, d178348, d179365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177422 q = 1) (hb : d178349 q = 1) : d179366 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177422, d178349, d179366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177422, d178349, d179366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177423 q = 1) (hb : d178350 q = 1) : d179367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177423, d178350, d179367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177423, d178350, d179367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177424 q = 1) (hb : d178351 q = 1) : d179368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177424, d178351, d179368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177424, d178351, d179368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177425 q = 1) (hb : d178352 q = 1) : d179369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177425, d178352, d179369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177425, d178352, d179369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40519 (p : Pattern) (ha : d177431 p = 1) (hb : d178358 p = 1) : d179311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177428 q = 1) (hb : d178355 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177428, d178355, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177428, d178355, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177429 q = 1) (hb : d178356 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177429, d178356, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177429, d178356, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177430 q = 1) (hb : d178357 q = 1) : d179310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177430, d178357, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177430, d178357, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177431 q = 1) (hb : d178358 q = 1) : d179311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177431, d178358, d179311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177431, d178358, d179311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40520 (p : Pattern) (ha : d177437 p = 1) (hb : d178364 p = 1) : d179376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177404 q = 1) (hb : d178329 q = 1) : d179332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177404, d178329, d179332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40512 q ha hb
    | true =>
      simp only [d177404, d178329, d179332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40510 q ha hb
  have h2 (q : Pattern) (ha : d177405 q = 1) (hb : d178330 q = 1) : d179333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177405, d178330, d179333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177405, d178330, d179333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177406 q = 1) (hb : d178331 q = 1) : d179334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177406, d178331, d179334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177406, d178331, d179334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177407 q = 1) (hb : d178332 q = 1) : d179335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177407, d178332, d179335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177407, d178332, d179335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177411 q = 1) (hb : d178336 q = 1) : d179339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177411, d178336, d179339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40513 q ha hb
    | true =>
      simp only [d177411, d178336, d179339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40511 q ha hb
  have h6 (q : Pattern) (ha : d177412 q = 1) (hb : d178337 q = 1) : d179340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177412, d178337, d179340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177412, d178337, d179340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177413 q = 1) (hb : d178338 q = 1) : d179341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177413, d178338, d179341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177413, d178338, d179341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177426 q = 1) (hb : d178353 q = 1) : d179370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177426, d178353, d179370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40518 q ha hb
    | true =>
      simp only [d177426, d178353, d179370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177384 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177427 q = 1) (hb : d178354 q = 1) : d179371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177427, d178354, d179371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177427, d178354, d179371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177432 q = 1) (hb : d178359 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177432, d178359, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40519 q ha hb
    | true =>
      simp only [d177432, d178359, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177433 q = 1) (hb : d178360 q = 1) : d179372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177433, d178360, d179372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177433, d178360, d179372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177434 q = 1) (hb : d178361 q = 1) : d179373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177434, d178361, d179373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177434, d178361, d179373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177435 q = 1) (hb : d178362 q = 1) : d179374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177435, d178362, d179374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177435, d178362, d179374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177436 q = 1) (hb : d178363 q = 1) : d179375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177436, d178363, d179375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177436, d178363, d179375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177437 q = 1) (hb : d178364 q = 1) : d179376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177437, d178364, d179376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177437, d178364, d179376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40521 (p : Pattern) (ha : d144487 p = 1) (hb : d160195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144423 q = 1) (hb : d160129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d144423, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144447 q = 1) (hb : d160153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144447, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144447, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144487 q = 1) (hb : d160195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144487, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144487, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40522 (p : Pattern) (ha : d144493 p = 1) (hb : d160201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144422 q = 1) (hb : d160128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144422, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144456 q = 1) (hb : d160162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d144456, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144456, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d144457 q = 1) (hb : d160163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d144457, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d144457, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d144493 q = 1) (hb : d160201 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d144493, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d144493, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40523 (p : Pattern) (ha : d177438 p = 1) (hb : d178365 p = 1) : d179377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177381 q = 1) (hb : d178306 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177381, d178306, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177402 q = 1) (hb : d178327 q = 1) : d179330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177402, d178327, d179330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177402, d178327, d179330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177438 q = 1) (hb : d178365 q = 1) : d179377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177438, d178365, d179377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177438, d178365, d179377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40524 (p : Pattern) (ha : d177443 p = 1) (hb : d178370 p = 1) : d179382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144416 q = 1) (hb : d160122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40496 q ha hb
    | true =>
      simp only [d144416, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144417 q = 1) (hb : d160123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144417, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177380 q = 1) (hb : d178305 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177380, d178305, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177408 q = 1) (hb : d178333 q = 1) : d179336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177408, d178333, d179336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177408, d178333, d179336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177409 q = 1) (hb : d178334 q = 1) : d179337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177409, d178334, d179337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177409, d178334, d179337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177443 q = 1) (hb : d178370 q = 1) : d179382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177443, d178370, d179382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177443, d178370, d179382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40525 (p : Pattern) (ha : d177447 p = 1) (hb : d178374 p = 1) : d179386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177420 q = 1) (hb : d178347 q = 1) : d179364 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177420, d178347, d179364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40517 q ha hb
    | true =>
      simp only [d177420, d178347, d179364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177421 q = 1) (hb : d178348 q = 1) : d179365 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177421, d178348, d179365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177421, d178348, d179365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177422 q = 1) (hb : d178349 q = 1) : d179366 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177422, d178349, d179366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177422, d178349, d179366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177423 q = 1) (hb : d178350 q = 1) : d179367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177423, d178350, d179367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177423, d178350, d179367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177424 q = 1) (hb : d178351 q = 1) : d179368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177424, d178351, d179368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177424, d178351, d179368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177447 q = 1) (hb : d178374 q = 1) : d179386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177447, d178374, d179386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177447, d178374, d179386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40526 (p : Pattern) (ha : d177450 p = 1) (hb : d178377 p = 1) : d179320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177378 q = 1) (hb : d178303 q = 1) : d179306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40505 q ha hb
    | true =>
      simp only [d177378, d178303, d179306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177379 q = 1) (hb : d178304 q = 1) : d179307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177379, d178304, d179307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177428 q = 1) (hb : d178355 q = 1) : d179308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177428, d178355, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177428, d178355, d179308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177429 q = 1) (hb : d178356 q = 1) : d179309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177429, d178356, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177429, d178356, d179309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177430 q = 1) (hb : d178357 q = 1) : d179310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177430, d178357, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177430, d178357, d179310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177450 q = 1) (hb : d178377 q = 1) : d179320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177450, d178377, d179320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177450, d178377, d179320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40527 (p : Pattern) (ha : d177456 p = 1) (hb : d178383 p = 1) : d179393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177404 q = 1) (hb : d178329 q = 1) : d179332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177404, d178329, d179332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40512 q ha hb
    | true =>
      simp only [d177404, d178329, d179332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40510 q ha hb
  have h2 (q : Pattern) (ha : d177405 q = 1) (hb : d178330 q = 1) : d179333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177405, d178330, d179333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177405, d178330, d179333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177406 q = 1) (hb : d178331 q = 1) : d179334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177406, d178331, d179334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177406, d178331, d179334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177407 q = 1) (hb : d178332 q = 1) : d179335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177407, d178332, d179335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177407, d178332, d179335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177411 q = 1) (hb : d178336 q = 1) : d179339 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177411, d178336, d179339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40513 q ha hb
    | true =>
      simp only [d177411, d178336, d179339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40511 q ha hb
  have h6 (q : Pattern) (ha : d177412 q = 1) (hb : d178337 q = 1) : d179340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177412, d178337, d179340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177412, d178337, d179340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177413 q = 1) (hb : d178338 q = 1) : d179341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177413, d178338, d179341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177413, d178338, d179341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177426 q = 1) (hb : d178353 q = 1) : d179370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177426, d178353, d179370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40518 q ha hb
    | true =>
      simp only [d177426, d178353, d179370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177384 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177427 q = 1) (hb : d178354 q = 1) : d179371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177427, d178354, d179371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177427, d178354, d179371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177432 q = 1) (hb : d178359 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177432, d178359, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40519 q ha hb
    | true =>
      simp only [d177432, d178359, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177433 q = 1) (hb : d178360 q = 1) : d179372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177433, d178360, d179372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177433, d178360, d179372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177434 q = 1) (hb : d178361 q = 1) : d179373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177434, d178361, d179373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177434, d178361, d179373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177435 q = 1) (hb : d178362 q = 1) : d179374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177435, d178362, d179374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177435, d178362, d179374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177436 q = 1) (hb : d178363 q = 1) : d179375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177436, d178363, d179375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177436, d178363, d179375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177439 q = 1) (hb : d178366 q = 1) : d179378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177439, d178366, d179378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40523 q ha hb
    | true =>
      simp only [d177439, d178366, d179378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40521 q ha hb
  have h17 (q : Pattern) (ha : d177440 q = 1) (hb : d178367 q = 1) : d179379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177440, d178367, d179379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177440, d178367, d179379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177441 q = 1) (hb : d178368 q = 1) : d179380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177441, d178368, d179380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177441, d178368, d179380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d177442 q = 1) (hb : d178369 q = 1) : d179381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177442, d178369, d179381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177442, d178369, d179381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177444 q = 1) (hb : d178371 q = 1) : d179383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177444, d178371, d179383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40524 q ha hb
    | true =>
      simp only [d177444, d178371, d179383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40522 q ha hb
  have h21 (q : Pattern) (ha : d177445 q = 1) (hb : d178372 q = 1) : d179384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177445, d178372, d179384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177445, d178372, d179384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d177446 q = 1) (hb : d178373 q = 1) : d179385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177446, d178373, d179385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177446, d178373, d179385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177448 q = 1) (hb : d178375 q = 1) : d179387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177448, d178375, d179387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40525 q ha hb
    | true =>
      simp only [d177448, d178375, d179387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40508 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d177393 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d177449 q = 1) (hb : d178376 q = 1) : d179388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177449, d178376, d179388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d177449, d178376, d179388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d177451 q = 1) (hb : d178378 q = 1) : d179321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177451, d178378, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40526 q ha hb
    | true =>
      simp only [d177451, d178378, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d177452 q = 1) (hb : d178379 q = 1) : d179389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177452, d178379, d179389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d177452, d178379, d179389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d177453 q = 1) (hb : d178380 q = 1) : d179390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177453, d178380, d179390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d177453, d178380, d179390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d177454 q = 1) (hb : d178381 q = 1) : d179391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177454, d178381, d179391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d177454, d178381, d179391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d177455 q = 1) (hb : d178382 q = 1) : d179392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177455, d178382, d179392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177455, d178382, d179392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d177456 q = 1) (hb : d178383 q = 1) : d179393 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177456, d178383, d179393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177456, d178383, d179393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40528 (p : Pattern) (ha : d177458 p = 1) (hb : d178385 p = 1) : d179395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177384 q = 1) (hb : d178309 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
    | true =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
  have h2 (q : Pattern) (ha : d177385 q = 1) (hb : d178310 q = 1) : d179313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177385, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177386 q = 1) (hb : d178311 q = 1) : d179314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177386, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177387 q = 1) (hb : d178312 q = 1) : d179315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177387, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177388 q = 1) (hb : d178313 q = 1) : d179316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177388, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144508 q = 1) (hb : d160216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144508, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
    | true =>
      simp only [d144508, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d144509 q = 1) (hb : d160217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d144509, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144509, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144510 q = 1) (hb : d160218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d144510, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d144510, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144511 q = 1) (hb : d160219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d144511, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144511, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144512 q = 1) (hb : d160220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d144512, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144512, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177458 q = 1) (hb : d178385 q = 1) : d179395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177458, d178385, d179395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177458, d178385, d179395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40529 (p : Pattern) (ha : d177465 p = 1) (hb : d178392 p = 1) : d179402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177448 q = 1) (hb : d178375 q = 1) : d179387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177448, d178375, d179387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40525 q ha hb
    | true =>
      simp only [d177448, d178375, d179387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40508 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177449 q = 1) (hb : d178376 q = 1) : d179388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177449, d178376, d179388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177449, d178376, d179388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177451 q = 1) (hb : d178378 q = 1) : d179321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177451, d178378, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40526 q ha hb
    | true =>
      simp only [d177451, d178378, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177452 q = 1) (hb : d178379 q = 1) : d179389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177452, d178379, d179389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177452, d178379, d179389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177453 q = 1) (hb : d178380 q = 1) : d179390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177453, d178380, d179390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177453, d178380, d179390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177463 q = 1) (hb : d178390 q = 1) : d179400 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177463, d178390, d179400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177463, d178390, d179400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177464 q = 1) (hb : d178391 q = 1) : d179401 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177464, d178391, d179401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177464, d178391, d179401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177465 q = 1) (hb : d178392 q = 1) : d179402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177465, d178392, d179402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177465, d178392, d179402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40530 (p : Pattern) (ha : d122850 p = 1) (hb : d178399 p = 1) : d179413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122850 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16356 q = 1) (hb : d122847 q = 1) : d179408 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d122847, d179408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16356, d122847, d179408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40515 q ha hb
  have h3 (q : Pattern) (ha : d9587 q = 1) (hb : d101177 q = 1) : d179352 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101177, d179352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40515 q ha hb
    | true =>
      simp only [d9587, d101177, d179352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16357 q = 1) (hb : d122848 q = 1) : d179409 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d122848, d179409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16357, d122848, d179409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9589 q = 1) (hb : d101179 q = 1) : d179353 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d101179, d179353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9589, d101179, d179353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16358 q = 1) (hb : d122849 q = 1) : d179410 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d122849, d179410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16358, d122849, d179410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16359 q = 1) (hb : d122850 q = 1) : d179411 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d122850, d179411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16359, d122850, d179411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d122850 q = 1) (hb : d178398 q = 1) : d179412 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178398, d179412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178398, d179412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122850 q = 1) (hb : d178399 q = 1) : d179413 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178399, d179413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178399, d179413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40531 (p : Pattern) (ha : d177480 p = 1) (hb : d178409 p = 1) : d179423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177471 q = 1) (hb : d178400 q = 1) : d179414 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177471, d178400, d179414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40530 q ha hb
    | true =>
      simp only [d177471, d178400, d179414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40489 q ha hb
  have h2 (q : Pattern) (ha : d177472 q = 1) (hb : d178401 q = 1) : d179415 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177472, d178401, d179415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177472, d178401, d179415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177473 q = 1) (hb : d178402 q = 1) : d179416 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177473, d178402, d179416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177473, d178402, d179416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177474 q = 1) (hb : d178403 q = 1) : d179417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177474, d178403, d179417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40489 q ha hb
    | true =>
      simp only [d177474, d178403, d179417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40501 q ha hb
  have h5 (q : Pattern) (ha : d177475 q = 1) (hb : d178404 q = 1) : d179418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177475, d178404, d179418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177475, d178404, d179418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177476 q = 1) (hb : d178405 q = 1) : d179419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177476, d178405, d179419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177476, d178405, d179419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177477 q = 1) (hb : d178406 q = 1) : d179420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177477, d178406, d179420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177477, d178406, d179420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144541 q = 1) (hb : d160253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40501 q ha hb
    | true =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d144542 q = 1) (hb : d160254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d144543 q = 1) (hb : d160255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177478 q = 1) (hb : d178407 q = 1) : d179421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177478, d178407, d179421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177478, d178407, d179421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d177479 q = 1) (hb : d178408 q = 1) : d179422 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177479, d178408, d179422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177479, d178408, d179422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d177480 q = 1) (hb : d178409 q = 1) : d179423 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177480, d178409, d179423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d177480, d178409, d179423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40532 (p : Pattern) (ha : d177484 p = 1) (hb : d178413 p = 1) : d179427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177474 q = 1) (hb : d178403 q = 1) : d179417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177474, d178403, d179417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40489 q ha hb
    | true =>
      simp only [d177474, d178403, d179417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40501 q ha hb
  have h2 (q : Pattern) (ha : d177475 q = 1) (hb : d178404 q = 1) : d179418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177475, d178404, d179418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177475, d178404, d179418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177476 q = 1) (hb : d178405 q = 1) : d179419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177476, d178405, d179419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177476, d178405, d179419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d144541 q = 1) (hb : d160253 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40501 q ha hb
    | true =>
      simp only [d144541, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d144542 q = 1) (hb : d160254 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144542, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d144543 q = 1) (hb : d160255 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144543, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177478 q = 1) (hb : d178407 q = 1) : d179421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177478, d178407, d179421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177478, d178407, d179421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d144549 q = 1) (hb : d160261 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d144549, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144549, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177483 q = 1) (hb : d178412 q = 1) : d179426 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177483, d178412, d179426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177483, d178412, d179426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177484 q = 1) (hb : d178413 q = 1) : d179427 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177484, d178413, d179427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d177484, d178413, d179427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro40533 (p : Pattern) (ha : d177490 p = 1) (hb : d178419 p = 1) : d179433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177481 q = 1) (hb : d178410 q = 1) : d179424 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177481, d178410, d179424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40531 q ha hb
    | true =>
      simp only [d177481, d178410, d179424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177482 q = 1) (hb : d178411 q = 1) : d179425 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177482, d178411, d179425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177482, d178411, d179425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177485 q = 1) (hb : d178414 q = 1) : d179428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40532 q ha hb
    | true =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177486 q = 1) (hb : d178415 q = 1) : d179429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177487 q = 1) (hb : d178416 q = 1) : d179430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177487, d178416, d179430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177487, d178416, d179430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177488 q = 1) (hb : d178417 q = 1) : d179431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177488, d178417, d179431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177488, d178417, d179431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177489 q = 1) (hb : d178418 q = 1) : d179432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177489, d178418, d179432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177489, d178418, d179432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177490 q = 1) (hb : d178419 q = 1) : d179433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177490, d178419, d179433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177490, d178419, d179433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40534 (p : Pattern) (ha : d177494 p = 1) (hb : d178423 p = 1) : d179437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177485 q = 1) (hb : d178414 q = 1) : d179428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40532 q ha hb
    | true =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177486 q = 1) (hb : d178415 q = 1) : d179429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d144560 q = 1) (hb : d160272 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d144560, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40502 q ha hb
    | true =>
      simp only [d144560, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d144561 q = 1) (hb : d160273 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d144561, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144561, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177491 q = 1) (hb : d178420 q = 1) : d179434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177491, d178420, d179434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177491, d178420, d179434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177492 q = 1) (hb : d178421 q = 1) : d179435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177492, d178421, d179435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177492, d178421, d179435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177493 q = 1) (hb : d178422 q = 1) : d179436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177493, d178422, d179436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177493, d178422, d179436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177494 q = 1) (hb : d178423 q = 1) : d179437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177494, d178423, d179437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177494, d178423, d179437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40535 (p : Pattern) (ha : d177501 p = 1) (hb : d178429 p = 1) : d179437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177485 q = 1) (hb : d178414 q = 1) : d179428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40532 q ha hb
    | true =>
      simp only [d177485, d178414, d179428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177486 q = 1) (hb : d178415 q = 1) : d179429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177486, d178415, d179429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177498 q = 1) (hb : d178426 q = 1) : d179434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177498, d178426, d179434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177498, d178426, d179434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177499 q = 1) (hb : d178427 q = 1) : d179435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177499, d178427, d179435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177499, d178427, d179435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177500 q = 1) (hb : d178428 q = 1) : d179436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177500, d178428, d179436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177500, d178428, d179436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177501 q = 1) (hb : d178429 q = 1) : d179437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177501, d178429, d179437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177501, d178429, d179437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40536 (p : Pattern) (ha : d177507 p = 1) (hb : d178435 p = 1) : d179445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177495 q = 1) (hb : d178424 q = 1) : d179438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177495, d178424, d179438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40533 q ha hb
    | true =>
      simp only [d177495, d178424, d179438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40534 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177497 q = 1) (hb : d178425 q = 1) : d179439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177497, d178425, d179439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177497, d178425, d179439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177502 q = 1) (hb : d178430 q = 1) : d179440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177502, d178430, d179440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40535 q ha hb
    | true =>
      simp only [d177502, d178430, d179440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177503 q = 1) (hb : d178431 q = 1) : d179441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177503, d178431, d179441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177503, d178431, d179441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177504 q = 1) (hb : d178432 q = 1) : d179442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177504, d178432, d179442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177504, d178432, d179442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177505 q = 1) (hb : d178433 q = 1) : d179443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177505, d178433, d179443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177505, d178433, d179443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177506 q = 1) (hb : d178434 q = 1) : d179444 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177506, d178434, d179444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177506, d178434, d179444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177507 q = 1) (hb : d178435 q = 1) : d179445 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177507, d178435, d179445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177507, d178435, d179445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40537 (p : Pattern) (ha : d177513 p = 1) (hb : d178441 p = 1) : d179451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177390 q = 1) (hb : d178315 q = 1) : d179318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177390, d178315, d179318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177390, d178315, d179318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40507 q ha hb
  have h2 (q : Pattern) (ha : d177391 q = 1) (hb : d178316 q = 1) : d179319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177391, d178316, d179319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177391, d178316, d179319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d177399 q = 1) (hb : d178324 q = 1) : d179327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177399, d178324, d179327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40507 q ha hb
    | true =>
      simp only [d177399, d178324, d179327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40509 q ha hb
  have h4 (q : Pattern) (ha : d177400 q = 1) (hb : d178325 q = 1) : d179328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177400, d178325, d179328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177400, d178325, d179328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177401 q = 1) (hb : d178326 q = 1) : d179329 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177401, d178326, d179329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177401, d178326, d179329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177457 q = 1) (hb : d178384 q = 1) : d179394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177457, d178384, d179394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40520 q ha hb
    | true =>
      simp only [d177457, d178384, d179394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40527 q ha hb
  have h7 (q : Pattern) (ha : d177459 q = 1) (hb : d178386 q = 1) : d179396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177459, d178386, d179396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40528 q ha hb
    | true =>
      simp only [d177459, d178386, d179396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40499 q ha hb
  have h8 (q : Pattern) (ha : d177460 q = 1) (hb : d178387 q = 1) : d179397 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177460, d178387, d179397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177460, d178387, d179397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177461 q = 1) (hb : d178388 q = 1) : d179398 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177461, d178388, d179398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177461, d178388, d179398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177462 q = 1) (hb : d178389 q = 1) : d179399 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177462, d178389, d179399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177462, d178389, d179399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177466 q = 1) (hb : d178393 q = 1) : d179403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177466, d178393, d179403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177466, d178393, d179403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40529 q ha hb
  have h12 (q : Pattern) (ha : d144529 q = 1) (hb : d160237 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144529, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144529, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40500 q ha hb
  have h13 (q : Pattern) (ha : d177467 q = 1) (hb : d178394 q = 1) : d179404 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177467, d178394, d179404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177467, d178394, d179404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177468 q = 1) (hb : d178395 q = 1) : d179405 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177468, d178395, d179405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177468, d178395, d179405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d177469 q = 1) (hb : d178396 q = 1) : d179406 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177469, d178396, d179406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d177469, d178396, d179406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d177470 q = 1) (hb : d178397 q = 1) : d179407 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177470, d178397, d179407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177470, d178397, d179407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177508 q = 1) (hb : d178436 q = 1) : d179446 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177508, d178436, d179446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177508, d178436, d179446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40536 q ha hb
  have h18 (q : Pattern) (ha : d144590 q = 1) (hb : d160301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d144590, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d144590, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40504 q ha hb
  have h19 (q : Pattern) (ha : d177509 q = 1) (hb : d178437 q = 1) : d179447 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177509, d178437, d179447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177509, d178437, d179447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177510 q = 1) (hb : d178438 q = 1) : d179448 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177510, d178438, d179448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177510, d178438, d179448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d177511 q = 1) (hb : d178439 q = 1) : d179449 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177511, d178439, d179449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d177511, d178439, d179449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d177512 q = 1) (hb : d178440 q = 1) : d179450 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177512, d178440, d179450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177512, d178440, d179450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177513 q = 1) (hb : d178441 q = 1) : d179451 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177513, d178441, d179451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177513, d178441, d179451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40538 (p : Pattern) (ha : d177519 p = 1) (hb : d178447 p = 1) : d179457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177514 q = 1) (hb : d178442 q = 1) : d179452 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177514, d178442, d179452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177514, d178442, d179452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40537 q ha hb
  have h2 (q : Pattern) (ha : d177515 q = 1) (hb : d178443 q = 1) : d179453 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177515, d178443, d179453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177515, d178443, d179453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177516 q = 1) (hb : d178444 q = 1) : d179454 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177516, d178444, d179454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177516, d178444, d179454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177517 q = 1) (hb : d178445 q = 1) : d179455 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177517, d178445, d179455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177517, d178445, d179455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177518 q = 1) (hb : d178446 q = 1) : d179456 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177518, d178446, d179456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177518, d178446, d179456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177519 q = 1) (hb : d178447 q = 1) : d179457 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177519, d178447, d179457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177519, d178447, d179457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40539 (p : Pattern) (ha : d1120 p = 1) (hb : d101320 p = 1) : d179477 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d18 q = 1) : d18 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d1104 q = 1) (hb : d101067 q = 1) : d179472 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d101067, d179472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40476 q ha hb
    | true =>
      simp only [d1104, d101067, d179472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1105 q = 1) (hb : d101068 q = 1) : d179473 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d101068, d179473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1105, d101068, d179473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1106 q = 1) (hb : d101316 q = 1) : d179474 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d101316, d179474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1106, d101316, d179474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d20 q = 1) : d20 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d135 q = 1) (hb : d101317 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d101317, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d135, d101317, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1107 q = 1) (hb : d101318 q = 1) : d179475 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d101318, d179475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1107, d101318, d179475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1108 q = 1) (hb : d101319 q = 1) : d179476 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d101319, d179476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1108, d101319, d179476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h21 (q : Pattern) (ha : d1120 q = 1) (hb : d101320 q = 1) : d179477 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d101320, d179477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1120, d101320, d179477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro40540 (p : Pattern) (ha : d122935 p = 1) (hb : d160318 p = 1) : d179483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d101321 q = 1) : d179478 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d101321, d179478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40539 q ha hb
    | true =>
      simp only [d1121, d101321, d179478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d101323 q = 1) : d179479 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d101323, d179479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d101323, d179479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d122934 q = 1) : d179480 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d122934, d179480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d122934, d179480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d122935 q = 1) : d179481 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d122935, d179481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d122935, d179481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d122935 q = 1) (hb : d160317 q = 1) : d179482 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d160317, d179482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d160317, d179482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122935 q = 1) (hb : d160318 q = 1) : d179483 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d160318, d179483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d160318, d179483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40541 (p : Pattern) (ha : d160332 p = 1) (hb : d177535 p = 1) : d179497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d160322 q = 1) (hb : d177525 q = 1) : d179487 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q hb ha
    | true =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160323 q = 1) (hb : d177526 q = 1) : d179488 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d160324 q = 1) (hb : d177527 q = 1) : d179489 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160326 q = 1) (hb : d177529 q = 1) : d179491 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160326, d177529, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160326, d177529, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160331 q = 1) (hb : d177534 q = 1) : d179496 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d160331, d177534, d179496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160331, d177534, d179496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d160332 q = 1) (hb : d177535 q = 1) : d179497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d160332, d177535, d179497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d160332, d177535, d179497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro40542 (p : Pattern) (ha : d160342 p = 1) (hb : d177545 p = 1) : d179507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160340 q = 1) (hb : d177543 q = 1) : d179505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160341 q = 1) (hb : d177544 q = 1) : d179506 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160341, d177544, d179506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160341, d177544, d179506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160342 q = 1) (hb : d177545 q = 1) : d179507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160342, d177545, d179507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160342, d177545, d179507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40543 (p : Pattern) (ha : d160352 p = 1) (hb : d177555 p = 1) : d179517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160340 q = 1) (hb : d177543 q = 1) : d179505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160341 q = 1) (hb : d177544 q = 1) : d179506 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160341, d177544, d179506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160341, d177544, d179506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160352 q = 1) (hb : d177555 q = 1) : d179517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160352, d177555, d179517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160352, d177555, d179517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40544 (p : Pattern) (ha : d160443 p = 1) (hb : d177647 p = 1) : d179614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160432 q = 1) (hb : d177636 q = 1) : d179603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160432, d177636, d179603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q ha hb
    | true =>
      simp only [d160432, d177636, d179603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160433 q = 1) (hb : d177637 q = 1) : d179604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160433, d177637, d179604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160433, d177637, d179604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160434 q = 1) (hb : d177638 q = 1) : d179605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160434, d177638, d179605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160434, d177638, d179605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160435 q = 1) (hb : d177639 q = 1) : d179606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160435, d177639, d179606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160435, d177639, d179606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160436 q = 1) (hb : d177640 q = 1) : d179607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160436, d177640, d179607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160436, d177640, d179607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160438 q = 1) (hb : d177642 q = 1) : d179609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160438, d177642, d179609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40543 q ha hb
    | true =>
      simp only [d160438, d177642, d179609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d160439 q = 1) (hb : d177643 q = 1) : d179610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160439, d177643, d179610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160439, d177643, d179610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160440 q = 1) (hb : d177644 q = 1) : d179611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160440, d177644, d179611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160440, d177644, d179611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d160441 q = 1) (hb : d177645 q = 1) : d179612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160441, d177645, d179612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160441, d177645, d179612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d160442 q = 1) (hb : d177646 q = 1) : d179613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160442, d177646, d179613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160442, d177646, d179613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d160443 q = 1) (hb : d177647 q = 1) : d179614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160443, d177647, d179614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160443, d177647, d179614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40545 (p : Pattern) (ha : d160452 p = 1) (hb : d177656 p = 1) : d179623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160438 q = 1) (hb : d177642 q = 1) : d179609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160438, d177642, d179609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40543 q ha hb
    | true =>
      simp only [d160438, d177642, d179609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160439 q = 1) (hb : d177643 q = 1) : d179610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160439, d177643, d179610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160439, d177643, d179610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160440 q = 1) (hb : d177644 q = 1) : d179611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160440, d177644, d179611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160440, d177644, d179611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160441 q = 1) (hb : d177645 q = 1) : d179612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160441, d177645, d179612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160441, d177645, d179612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160442 q = 1) (hb : d177646 q = 1) : d179613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160442, d177646, d179613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160442, d177646, d179613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160452 q = 1) (hb : d177656 q = 1) : d179623 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160452, d177656, d179623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160452, d177656, d179623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40546 (p : Pattern) (ha : d123132 p = 1) (hb : d160472 p = 1) : d179653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d123129 q = 1) : d179648 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d123129, d179648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d123129, d179648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40539 q ha hb
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d101321 q = 1) : d179478 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d101321, d179478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40539 q ha hb
    | true =>
      simp only [d1121, d101321, d179478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d123130 q = 1) : d179649 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d123130, d179649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d123130, d179649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d101323 q = 1) : d179479 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d101323, d179479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, d101323, d179479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d123131 q = 1) : d179650 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d123131, d179650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d123131, d179650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1394 q = 1) (hb : d123132 q = 1) : d179651 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d123132, d179651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d123132, d179651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123132 q = 1) (hb : d160471 q = 1) : d179652 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d160471, d179652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d160471, d179652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123132 q = 1) (hb : d160472 q = 1) : d179653 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d160472, d179653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d160472, d179653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40547 (p : Pattern) (ha : d160494 p = 1) (hb : d177687 p = 1) : d179675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d160476 q = 1) (hb : d177669 q = 1) : d179657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q hb ha
    | true =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160477 q = 1) (hb : d177670 q = 1) : d179658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d160478 q = 1) (hb : d177671 q = 1) : d179659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160484 q = 1) (hb : d177677 q = 1) : d179665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160484, d177677, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160484, d177677, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160493 q = 1) (hb : d177686 q = 1) : d179674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d160493, d177686, d179674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160493, d177686, d179674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d160494 q = 1) (hb : d177687 q = 1) : d179675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d160494, d177687, d179675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d160494, d177687, d179675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro40548 (p : Pattern) (ha : d160517 p = 1) (hb : d177698 p = 1) : d179698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160495 q = 1) (hb : d177688 q = 1) : d179676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160495, d177688, d179676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40547 q ha hb
    | true =>
      simp only [d160495, d177688, d179676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160496 q = 1) (hb : d177689 q = 1) : d179677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160496, d177689, d179677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160496, d177689, d179677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160514 q = 1) (hb : d177695 q = 1) : d179695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160514, d177695, d179695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160514, d177695, d179695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160515 q = 1) (hb : d177696 q = 1) : d179696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160515, d177696, d179696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160515, d177696, d179696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160516 q = 1) (hb : d177697 q = 1) : d179697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160516, d177697, d179697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160516, d177697, d179697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160517 q = 1) (hb : d177698 q = 1) : d179698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160517, d177698, d179698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160517, d177698, d179698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40549 (p : Pattern) (ha : d160523 p = 1) (hb : d177725 p = 1) : d179704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160518 q = 1) (hb : d177720 q = 1) : d179699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160518, d177720, d179699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40548 q ha hb
    | true =>
      simp only [d160518, d177720, d179699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160519 q = 1) (hb : d177721 q = 1) : d179700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160519, d177721, d179700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160519, d177721, d179700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160520 q = 1) (hb : d177722 q = 1) : d179701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160520, d177722, d179701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160520, d177722, d179701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160521 q = 1) (hb : d177723 q = 1) : d179702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160521, d177723, d179702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160521, d177723, d179702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160522 q = 1) (hb : d177724 q = 1) : d179703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160522, d177724, d179703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160522, d177724, d179703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160523 q = 1) (hb : d177725 q = 1) : d179704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160523, d177725, d179704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160523, d177725, d179704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40550 (p : Pattern) (ha : d9788 p = 1) (hb : d101298 p = 1) : d179465 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1093 q = 1) : d1093 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d1094 q = 1) (hb : d101161 q = 1) : d179460 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d101161, d179460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40514 q ha hb
    | true =>
      simp only [d1094, d101161, d179460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1095 q = 1) (hb : d101162 q = 1) : d179461 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d101162, d179461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1095, d101162, d179461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1096 q = 1) (hb : d101289 q = 1) : d179462 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d101289, d179462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1096, d101289, d179462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d539 q = 1) : d539 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d1097 q = 1) (hb : d101290 q = 1) : d179463 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d101290, d179463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1097, d101290, d179463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1098 q = 1) (hb : d101291 q = 1) : d179464 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d101291, d179464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1098, d101291, d179464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9772 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h11 (q : Pattern) (ha : d9773 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9774 q = 1) (hb : d101295 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9775 q = 1) (hb : d101296 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9776 q = 1) (hb : d101297 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d9788 q = 1) (hb : d101298 q = 1) : d179465 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9788, d101298, d179465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9788, d101298, d179465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro40551 (p : Pattern) (ha : d122930 p = 1) (hb : d178451 p = 1) : d179471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122930 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9789 q = 1) (hb : d101299 q = 1) : d179466 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101299, d179466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40550 q ha hb
    | true =>
      simp only [d9789, d101299, d179466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9791 q = 1) (hb : d101301 q = 1) : d179467 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101301, d179467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9791, d101301, d179467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16438 q = 1) (hb : d122929 q = 1) : d179468 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d122929, d179468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16438, d122929, d179468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16439 q = 1) (hb : d122930 q = 1) : d179469 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d122930, d179469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16439, d122930, d179469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d122930 q = 1) (hb : d178450 q = 1) : d179470 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178450, d179470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178450, d179470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122930 q = 1) (hb : d178451 q = 1) : d179471 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178451, d179471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178451, d179471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40552 (p : Pattern) (ha : d177531 p = 1) (hb : d178457 p = 1) : d179493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177522 q = 1) (hb : d178452 q = 1) : d179484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40551 q ha hb
    | true =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q ha hb
  have h2 (q : Pattern) (ha : d177523 q = 1) (hb : d178453 q = 1) : d179485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177524 q = 1) (hb : d178454 q = 1) : d179486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160322 q = 1) (hb : d177525 q = 1) : d179487 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q hb ha
    | true =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160323 q = 1) (hb : d177526 q = 1) : d179488 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160324 q = 1) (hb : d177527 q = 1) : d179489 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177528 q = 1) (hb : d178455 q = 1) : d179490 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d160326 q = 1) (hb : d177529 q = 1) : d179491 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160326, d177529, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160326, d177529, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d177530 q = 1) (hb : d178456 q = 1) : d179492 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177530, d178456, d179492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177530, d178456, d179492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177531 q = 1) (hb : d178457 q = 1) : d179493 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177531, d178457, d179493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177531, d178457, d179493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40553 (p : Pattern) (ha : d177541 p = 1) (hb : d178463 p = 1) : d179503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177539 q = 1) (hb : d178461 q = 1) : d179501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177540 q = 1) (hb : d178462 q = 1) : d179502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177540, d178462, d179502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177540, d178462, d179502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177541 q = 1) (hb : d178463 q = 1) : d179503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177541, d178463, d179503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177541, d178463, d179503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40554 (p : Pattern) (ha : d177551 p = 1) (hb : d178469 p = 1) : d179513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177546 q = 1) (hb : d178464 q = 1) : d179508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
    | true =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q hb ha
  have h2 (q : Pattern) (ha : d177547 q = 1) (hb : d178465 q = 1) : d179509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177548 q = 1) (hb : d178466 q = 1) : d179510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177549 q = 1) (hb : d178467 q = 1) : d179511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177550 q = 1) (hb : d178468 q = 1) : d179512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177551 q = 1) (hb : d178469 q = 1) : d179513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177551, d178469, d179513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177551, d178469, d179513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40555 (p : Pattern) (ha : d177554 p = 1) (hb : d178472 p = 1) : d179516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177539 q = 1) (hb : d178461 q = 1) : d179501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177540 q = 1) (hb : d178462 q = 1) : d179502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177540, d178462, d179502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177540, d178462, d179502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177554 q = 1) (hb : d178472 q = 1) : d179516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177554, d178472, d179516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177554, d178472, d179516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40556 (p : Pattern) (ha : d177561 p = 1) (hb : d178478 p = 1) : d179523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177546 q = 1) (hb : d178464 q = 1) : d179508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
    | true =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q hb ha
  have h2 (q : Pattern) (ha : d177547 q = 1) (hb : d178465 q = 1) : d179509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177548 q = 1) (hb : d178466 q = 1) : d179510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177549 q = 1) (hb : d178467 q = 1) : d179511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177550 q = 1) (hb : d178468 q = 1) : d179512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177556 q = 1) (hb : d178473 q = 1) : d179518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40555 q ha hb
    | true =>
      simp only [d177556, d178473, d179518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40543 q hb ha
  have h7 (q : Pattern) (ha : d177557 q = 1) (hb : d178474 q = 1) : d179519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177557, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177557, d178474, d179519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177558 q = 1) (hb : d178475 q = 1) : d179520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177558, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177558, d178475, d179520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177559 q = 1) (hb : d178476 q = 1) : d179521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177559, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177559, d178476, d179521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177560 q = 1) (hb : d178477 q = 1) : d179522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177560, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177560, d178477, d179522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177561 q = 1) (hb : d178478 q = 1) : d179523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177561, d178478, d179523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177561, d178478, d179523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40557 (p : Pattern) (ha : d160365 p = 1) (hb : d177568 p = 1) : d179530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160340 q = 1) (hb : d177543 q = 1) : d179505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160364 q = 1) (hb : d177567 q = 1) : d179529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160364, d177567, d179529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160364, d177567, d179529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160365 q = 1) (hb : d177568 q = 1) : d179530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160365, d177568, d179530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160365, d177568, d179530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40558 (p : Pattern) (ha : d160375 p = 1) (hb : d177578 p = 1) : d179540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160373 q = 1) (hb : d177576 q = 1) : d179538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160373, d177576, d179538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160373, d177576, d179538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160374 q = 1) (hb : d177577 q = 1) : d179539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160374, d177577, d179539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160374, d177577, d179539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160375 q = 1) (hb : d177578 q = 1) : d179540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160375, d177578, d179540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160375, d177578, d179540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40559 (p : Pattern) (ha : d177566 p = 1) (hb : d178483 p = 1) : d179528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177539 q = 1) (hb : d178461 q = 1) : d179501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177565 q = 1) (hb : d178482 q = 1) : d179527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177565, d178482, d179527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177565, d178482, d179527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177566 q = 1) (hb : d178483 q = 1) : d179528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177566, d178483, d179528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177566, d178483, d179528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40560 (p : Pattern) (ha : d177575 p = 1) (hb : d178490 p = 1) : d179537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177573 q = 1) (hb : d178488 q = 1) : d179535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177573, d178488, d179535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177573, d178488, d179535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177574 q = 1) (hb : d178489 q = 1) : d179536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177574, d178489, d179536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177574, d178489, d179536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177575 q = 1) (hb : d178490 q = 1) : d179537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177575, d178490, d179537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177575, d178490, d179537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40561 (p : Pattern) (ha : d122935 p = 1) (hb : d178500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14763 q = 1) (hb : d122934 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14763, d122934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14764 q = 1) (hb : d122935 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14764, d122935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d122935 q = 1) (hb : d178499 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122935 q = 1) (hb : d178500 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40562 (p : Pattern) (ha : d9752 p = 1) (hb : d101283 p = 1) : d179547 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1089 q = 1) : d1089 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d1090 q = 1) (hb : d101280 q = 1) : d179544 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d101280, d179544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1090, d101280, d179544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d830 q = 1) : d830 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d1091 q = 1) (hb : d101281 q = 1) : d179545 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d101281, d179545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1091, d101281, d179545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1092 q = 1) (hb : d101282 q = 1) : d179546 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d101282, d179546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1092, d101282, d179546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9581 q = 1) (hb : d101161 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9582 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9749 q = 1) (hb : d101270 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9749, d101270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9749, d101270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9750 q = 1) (hb : d101271 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9750, d101271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9750, d101271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9751 q = 1) (hb : d101272 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9751, d101272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9751, d101272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9752 q = 1) (hb : d101283 q = 1) : d179547 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9752, d101283, d179547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9752, d101283, d179547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro40563 (p : Pattern) (ha : d123008 p = 1) (hb : d178495 p = 1) : d179553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9753 q = 1) (hb : d101284 q = 1) : d179548 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101284, d179548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40562 q ha hb
    | true =>
      simp only [d9753, d101284, d179548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9755 q = 1) (hb : d101286 q = 1) : d179549 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101286, d179549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9755, d101286, d179549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16507 q = 1) (hb : d123007 q = 1) : d179550 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d123007, d179550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16507, d123007, d179550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16508 q = 1) (hb : d123008 q = 1) : d179551 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d123008, d179551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16508, d123008, d179551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123008 q = 1) (hb : d178494 q = 1) : d179552 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178494, d179552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178494, d179552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123008 q = 1) (hb : d178495 q = 1) : d179553 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178495, d179553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178495, d179553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40564 (p : Pattern) (ha : d177587 p = 1) (hb : d178506 p = 1) : d179562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177582 q = 1) (hb : d178496 q = 1) : d179554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177582, d178496, d179554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40563 q ha hb
    | true =>
      simp only [d177582, d178496, d179554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40551 q ha hb
  have h2 (q : Pattern) (ha : d177583 q = 1) (hb : d178497 q = 1) : d179555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177583, d178497, d179555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177583, d178497, d179555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177584 q = 1) (hb : d178498 q = 1) : d179556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177584, d178498, d179556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177584, d178498, d179556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177522 q = 1) (hb : d178501 q = 1) : d179557 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177522, d178501, d179557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40551 q ha hb
    | true =>
      simp only [d177522, d178501, d179557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40561 q ha hb
  have h5 (q : Pattern) (ha : d177523 q = 1) (hb : d178502 q = 1) : d179558 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177523, d178502, d179558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177523, d178502, d179558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177524 q = 1) (hb : d178503 q = 1) : d179559 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177524, d178503, d179559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177524, d178503, d179559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177585 q = 1) (hb : d178504 q = 1) : d179560 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177585, d178504, d179560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177585, d178504, d179560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177522 q = 1) (hb : d178452 q = 1) : d179484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40551 q ha hb
    | true =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q ha hb
  have h9 (q : Pattern) (ha : d177523 q = 1) (hb : d178453 q = 1) : d179485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177524 q = 1) (hb : d178454 q = 1) : d179486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d160322 q = 1) (hb : d177525 q = 1) : d179487 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q hb ha
    | true =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d160323 q = 1) (hb : d177526 q = 1) : d179488 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d160324 q = 1) (hb : d177527 q = 1) : d179489 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177528 q = 1) (hb : d178455 q = 1) : d179490 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177586 q = 1) (hb : d178505 q = 1) : d179561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177586, d178505, d179561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177586, d178505, d179561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177587 q = 1) (hb : d178506 q = 1) : d179562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177587, d178506, d179562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177587, d178506, d179562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro40565 (p : Pattern) (ha : d177593 p = 1) (hb : d178512 p = 1) : d179568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177588 q = 1) (hb : d178507 q = 1) : d179563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177588, d178507, d179563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40564 q ha hb
    | true =>
      simp only [d177588, d178507, d179563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177589 q = 1) (hb : d178508 q = 1) : d179564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177589, d178508, d179564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177589, d178508, d179564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177590 q = 1) (hb : d178509 q = 1) : d179565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177590, d178509, d179565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177590, d178509, d179565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177591 q = 1) (hb : d178510 q = 1) : d179566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177591, d178510, d179566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177591, d178510, d179566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177592 q = 1) (hb : d178511 q = 1) : d179567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177592, d178511, d179567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177592, d178511, d179567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177593 q = 1) (hb : d178512 q = 1) : d179568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177593, d178512, d179568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177593, d178512, d179568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40566 (p : Pattern) (ha : d177601 p = 1) (hb : d178457 p = 1) : d179493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177522 q = 1) (hb : d178452 q = 1) : d179484 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40551 q ha hb
    | true =>
      simp only [d177522, d178452, d179484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q ha hb
  have h2 (q : Pattern) (ha : d177523 q = 1) (hb : d178453 q = 1) : d179485 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177523, d178453, d179485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177524 q = 1) (hb : d178454 q = 1) : d179486 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177524, d178454, d179486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160322 q = 1) (hb : d177525 q = 1) : d179487 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q hb ha
    | true =>
      simp only [d160322, d177525, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160323 q = 1) (hb : d177526 q = 1) : d179488 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160323, d177526, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160324 q = 1) (hb : d177527 q = 1) : d179489 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160324, d177527, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177528 q = 1) (hb : d178455 q = 1) : d179490 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177528, d178455, d179490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d160322 q = 1) (hb : d177596 q = 1) : d179487 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160322, d177596, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40540 q hb ha
    | true =>
      simp only [d160322, d177596, d179487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d160323 q = 1) (hb : d177597 q = 1) : d179488 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160323, d177597, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160323, d177597, d179488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d160324 q = 1) (hb : d177598 q = 1) : d179489 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160324, d177598, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160324, d177598, d179489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d160326 q = 1) (hb : d177599 q = 1) : d179491 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160326, d177599, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d160326, d177599, d179491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d177600 q = 1) (hb : d178456 q = 1) : d179492 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177600, d178456, d179492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177600, d178456, d179492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177601 q = 1) (hb : d178457 q = 1) : d179493 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177601, d178457, d179493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177601, d178457, d179493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40567 (p : Pattern) (ha : d177607 p = 1) (hb : d178518 p = 1) : d179574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177602 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177602, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40566 q ha hb
    | true =>
      simp only [d177602, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177603 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177603, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177603, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177604 q = 1) (hb : d178515 q = 1) : d179571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177604, d178515, d179571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177604, d178515, d179571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177605 q = 1) (hb : d178516 q = 1) : d179572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177605, d178516, d179572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177605, d178516, d179572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177606 q = 1) (hb : d178517 q = 1) : d179573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177606, d178517, d179573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177606, d178517, d179573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177607 q = 1) (hb : d178518 q = 1) : d179574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177607, d178518, d179574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177607, d178518, d179574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40568 (p : Pattern) (ha : d177613 p = 1) (hb : d178524 p = 1) : d179580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177569 q = 1) (hb : d178484 q = 1) : d179531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177569, d178484, d179531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40559 q ha hb
    | true =>
      simp only [d177569, d178484, d179531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40557 q hb ha
  have h2 (q : Pattern) (ha : d177570 q = 1) (hb : d178485 q = 1) : d179532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177570, d178485, d179532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177570, d178485, d179532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177571 q = 1) (hb : d178486 q = 1) : d179533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177571, d178486, d179533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177571, d178486, d179533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177572 q = 1) (hb : d178487 q = 1) : d179534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177572, d178487, d179534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177572, d178487, d179534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177579 q = 1) (hb : d178491 q = 1) : d179541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177579, d178491, d179541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40560 q ha hb
    | true =>
      simp only [d177579, d178491, d179541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40558 q hb ha
  have h6 (q : Pattern) (ha : d177580 q = 1) (hb : d178492 q = 1) : d179542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177580, d178492, d179542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177580, d178492, d179542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177581 q = 1) (hb : d178493 q = 1) : d179543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177581, d178493, d179543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177581, d178493, d179543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177594 q = 1) (hb : d178513 q = 1) : d179569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177594, d178513, d179569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40565 q ha hb
    | true =>
      simp only [d177594, d178513, d179569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177546 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177595 q = 1) (hb : d178514 q = 1) : d179570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177595, d178514, d179570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177595, d178514, d179570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177608 q = 1) (hb : d178519 q = 1) : d179575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177608, d178519, d179575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40567 q ha hb
    | true =>
      simp only [d177608, d178519, d179575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177609 q = 1) (hb : d178520 q = 1) : d179576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177609, d178520, d179576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177609, d178520, d179576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177610 q = 1) (hb : d178521 q = 1) : d179577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177610, d178521, d179577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177610, d178521, d179577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177611 q = 1) (hb : d178522 q = 1) : d179578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177611, d178522, d179578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177611, d178522, d179578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177612 q = 1) (hb : d178523 q = 1) : d179579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177612, d178523, d179579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177612, d178523, d179579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177613 q = 1) (hb : d178524 q = 1) : d179580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177613, d178524, d179580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177613, d178524, d179580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40569 (p : Pattern) (ha : d160411 p = 1) (hb : d177615 p = 1) : d179582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160340 q = 1) (hb : d177543 q = 1) : d179505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160340, d177543, d179505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d160364 q = 1) (hb : d177567 q = 1) : d179529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160364, d177567, d179529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160364, d177567, d179529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160411 q = 1) (hb : d177615 q = 1) : d179582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160411, d177615, d179582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160411, d177615, d179582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40570 (p : Pattern) (ha : d160417 p = 1) (hb : d177621 p = 1) : d179588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160339 q = 1) (hb : d177542 q = 1) : d179504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d160339, d177542, d179504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160373 q = 1) (hb : d177576 q = 1) : d179538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d160373, d177576, d179538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160373, d177576, d179538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d160374 q = 1) (hb : d177577 q = 1) : d179539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d160374, d177577, d179539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160374, d177577, d179539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d160417 q = 1) (hb : d177621 q = 1) : d179588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d160417, d177621, d179588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d160417, d177621, d179588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40571 (p : Pattern) (ha : d177614 p = 1) (hb : d178525 p = 1) : d179581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177539 q = 1) (hb : d178461 q = 1) : d179501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177539, d178461, d179501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177565 q = 1) (hb : d178482 q = 1) : d179527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177565, d178482, d179527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177565, d178482, d179527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177614 q = 1) (hb : d178525 q = 1) : d179581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177614, d178525, d179581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177614, d178525, d179581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40572 (p : Pattern) (ha : d177620 p = 1) (hb : d178530 p = 1) : d179587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160333 q = 1) (hb : d177536 q = 1) : d179498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40541 q ha hb
    | true =>
      simp only [d160333, d177536, d179498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160334 q = 1) (hb : d177537 q = 1) : d179499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160334, d177537, d179499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177538 q = 1) (hb : d178460 q = 1) : d179500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177538, d178460, d179500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177573 q = 1) (hb : d178488 q = 1) : d179535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177573, d178488, d179535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177573, d178488, d179535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177574 q = 1) (hb : d178489 q = 1) : d179536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177574, d178489, d179536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177574, d178489, d179536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177620 q = 1) (hb : d178530 q = 1) : d179587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177620, d178530, d179587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177620, d178530, d179587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40573 (p : Pattern) (ha : d177625 p = 1) (hb : d178534 p = 1) : d179592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177588 q = 1) (hb : d178507 q = 1) : d179563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177588, d178507, d179563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40564 q ha hb
    | true =>
      simp only [d177588, d178507, d179563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177589 q = 1) (hb : d178508 q = 1) : d179564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177589, d178508, d179564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177589, d178508, d179564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177532 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40552 q ha hb
    | true =>
      simp only [d177532, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177533 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177533, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177590 q = 1) (hb : d178509 q = 1) : d179565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177590, d178509, d179565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177590, d178509, d179565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177591 q = 1) (hb : d178510 q = 1) : d179566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177591, d178510, d179566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177591, d178510, d179566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177592 q = 1) (hb : d178511 q = 1) : d179567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177592, d178511, d179567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177592, d178511, d179567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177625 q = 1) (hb : d178534 q = 1) : d179592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177625, d178534, d179592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177625, d178534, d179592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40574 (p : Pattern) (ha : d177628 p = 1) (hb : d178537 p = 1) : d179595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177602 q = 1) (hb : d178458 q = 1) : d179494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177602, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40566 q ha hb
    | true =>
      simp only [d177602, d178458, d179494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177603 q = 1) (hb : d178459 q = 1) : d179495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177603, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177603, d178459, d179495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177604 q = 1) (hb : d178515 q = 1) : d179571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177604, d178515, d179571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177604, d178515, d179571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177605 q = 1) (hb : d178516 q = 1) : d179572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177605, d178516, d179572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177605, d178516, d179572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177606 q = 1) (hb : d178517 q = 1) : d179573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177606, d178517, d179573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177606, d178517, d179573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177628 q = 1) (hb : d178537 q = 1) : d179595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177628, d178537, d179595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177628, d178537, d179595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40575 (p : Pattern) (ha : d177634 p = 1) (hb : d178543 p = 1) : d179601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177569 q = 1) (hb : d178484 q = 1) : d179531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177569, d178484, d179531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40559 q ha hb
    | true =>
      simp only [d177569, d178484, d179531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40557 q hb ha
  have h2 (q : Pattern) (ha : d177570 q = 1) (hb : d178485 q = 1) : d179532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177570, d178485, d179532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177570, d178485, d179532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177571 q = 1) (hb : d178486 q = 1) : d179533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177571, d178486, d179533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177571, d178486, d179533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177572 q = 1) (hb : d178487 q = 1) : d179534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177572, d178487, d179534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177572, d178487, d179534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177579 q = 1) (hb : d178491 q = 1) : d179541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177579, d178491, d179541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40560 q ha hb
    | true =>
      simp only [d177579, d178491, d179541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40558 q hb ha
  have h6 (q : Pattern) (ha : d177580 q = 1) (hb : d178492 q = 1) : d179542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177580, d178492, d179542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177580, d178492, d179542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177581 q = 1) (hb : d178493 q = 1) : d179543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177581, d178493, d179543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177581, d178493, d179543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177594 q = 1) (hb : d178513 q = 1) : d179569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177594, d178513, d179569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40565 q ha hb
    | true =>
      simp only [d177594, d178513, d179569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177546 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177595 q = 1) (hb : d178514 q = 1) : d179570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177595, d178514, d179570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177595, d178514, d179570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177608 q = 1) (hb : d178519 q = 1) : d179575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177608, d178519, d179575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40567 q ha hb
    | true =>
      simp only [d177608, d178519, d179575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177609 q = 1) (hb : d178520 q = 1) : d179576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177609, d178520, d179576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177609, d178520, d179576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177610 q = 1) (hb : d178521 q = 1) : d179577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177610, d178521, d179577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177610, d178521, d179577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177611 q = 1) (hb : d178522 q = 1) : d179578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177611, d178522, d179578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177611, d178522, d179578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177612 q = 1) (hb : d178523 q = 1) : d179579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177612, d178523, d179579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177612, d178523, d179579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177616 q = 1) (hb : d178526 q = 1) : d179583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177616, d178526, d179583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40571 q ha hb
    | true =>
      simp only [d177616, d178526, d179583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40569 q hb ha
  have h17 (q : Pattern) (ha : d177617 q = 1) (hb : d178527 q = 1) : d179584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177617, d178527, d179584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177617, d178527, d179584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177618 q = 1) (hb : d178528 q = 1) : d179585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177618, d178528, d179585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177618, d178528, d179585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d177619 q = 1) (hb : d178529 q = 1) : d179586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177619, d178529, d179586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177619, d178529, d179586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177622 q = 1) (hb : d178531 q = 1) : d179589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177622, d178531, d179589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40572 q ha hb
    | true =>
      simp only [d177622, d178531, d179589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40570 q hb ha
  have h21 (q : Pattern) (ha : d177623 q = 1) (hb : d178532 q = 1) : d179590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177623, d178532, d179590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177623, d178532, d179590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d177624 q = 1) (hb : d178533 q = 1) : d179591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177624, d178533, d179591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177624, d178533, d179591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177626 q = 1) (hb : d178535 q = 1) : d179593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177626, d178535, d179593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40573 q ha hb
    | true =>
      simp only [d177626, d178535, d179593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40555 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d177556 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d177627 q = 1) (hb : d178536 q = 1) : d179594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177627, d178536, d179594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d177627, d178536, d179594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d177629 q = 1) (hb : d178538 q = 1) : d179596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177629, d178538, d179596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40574 q ha hb
    | true =>
      simp only [d177629, d178538, d179596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d177630 q = 1) (hb : d178539 q = 1) : d179597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177630, d178539, d179597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d177630, d178539, d179597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d177631 q = 1) (hb : d178540 q = 1) : d179598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177631, d178540, d179598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d177631, d178540, d179598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d177632 q = 1) (hb : d178541 q = 1) : d179599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177632, d178541, d179599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d177632, d178541, d179599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d177633 q = 1) (hb : d178542 q = 1) : d179600 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177633, d178542, d179600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177633, d178542, d179600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d177634 q = 1) (hb : d178543 q = 1) : d179601 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177634, d178543, d179601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177634, d178543, d179601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40576 (p : Pattern) (ha : d177641 p = 1) (hb : d178545 p = 1) : d179608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177546 q = 1) (hb : d178464 q = 1) : d179508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40553 q ha hb
    | true =>
      simp only [d177546, d178464, d179508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q hb ha
  have h2 (q : Pattern) (ha : d177547 q = 1) (hb : d178465 q = 1) : d179509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177547, d178465, d179509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177548 q = 1) (hb : d178466 q = 1) : d179510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177548, d178466, d179510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177549 q = 1) (hb : d178467 q = 1) : d179511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177549, d178467, d179511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177550 q = 1) (hb : d178468 q = 1) : d179512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177550, d178468, d179512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160432 q = 1) (hb : d177636 q = 1) : d179603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d160432, d177636, d179603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40542 q ha hb
    | true =>
      simp only [d160432, d177636, d179603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d160433 q = 1) (hb : d177637 q = 1) : d179604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160433, d177637, d179604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160433, d177637, d179604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160434 q = 1) (hb : d177638 q = 1) : d179605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160434, d177638, d179605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160434, d177638, d179605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d160435 q = 1) (hb : d177639 q = 1) : d179606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160435, d177639, d179606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160435, d177639, d179606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d160436 q = 1) (hb : d177640 q = 1) : d179607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160436, d177640, d179607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160436, d177640, d179607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177641 q = 1) (hb : d178545 q = 1) : d179608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177641, d178545, d179608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177641, d178545, d179608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro40577 (p : Pattern) (ha : d177654 p = 1) (hb : d178552 p = 1) : d179621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177626 q = 1) (hb : d178535 q = 1) : d179593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177626, d178535, d179593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40573 q ha hb
    | true =>
      simp only [d177626, d178535, d179593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40555 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177556 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177627 q = 1) (hb : d178536 q = 1) : d179594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177627, d178536, d179594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177627, d178536, d179594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177629 q = 1) (hb : d178538 q = 1) : d179596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177629, d178538, d179596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40574 q ha hb
    | true =>
      simp only [d177629, d178538, d179596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177630 q = 1) (hb : d178539 q = 1) : d179597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177630, d178539, d179597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177630, d178539, d179597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177631 q = 1) (hb : d178540 q = 1) : d179598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177631, d178540, d179598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177631, d178540, d179598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177652 q = 1) (hb : d178550 q = 1) : d179619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177652, d178550, d179619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177652, d178550, d179619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177653 q = 1) (hb : d178551 q = 1) : d179620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177653, d178551, d179620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177653, d178551, d179620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177654 q = 1) (hb : d178552 q = 1) : d179621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177654, d178552, d179621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177654, d178552, d179621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40578 (p : Pattern) (ha : d123115 p = 1) (hb : d178559 p = 1) : d179634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16649 q = 1) (hb : d123112 q = 1) : d179629 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d123112, d179629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16649, d123112, d179629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40562 q ha hb
  have h3 (q : Pattern) (ha : d9753 q = 1) (hb : d101284 q = 1) : d179548 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101284, d179548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40562 q ha hb
    | true =>
      simp only [d9753, d101284, d179548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16650 q = 1) (hb : d123113 q = 1) : d179630 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d123113, d179630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16650, d123113, d179630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9755 q = 1) (hb : d101286 q = 1) : d179549 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101286, d179549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9755, d101286, d179549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16651 q = 1) (hb : d123114 q = 1) : d179631 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d123114, d179631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16651, d123114, d179631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16652 q = 1) (hb : d123115 q = 1) : d179632 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d123115, d179632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16652, d123115, d179632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123115 q = 1) (hb : d178558 q = 1) : d179633 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178558, d179633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178558, d179633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123115 q = 1) (hb : d178559 q = 1) : d179634 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178559, d179634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178559, d179634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40579 (p : Pattern) (ha : d123122 p = 1) (hb : d178561 p = 1) : d179640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16656 q = 1) (hb : d123119 q = 1) : d179635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d123119, d179635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16656, d123119, d179635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40550 q ha hb
  have h3 (q : Pattern) (ha : d9789 q = 1) (hb : d101299 q = 1) : d179466 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101299, d179466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40550 q ha hb
    | true =>
      simp only [d9789, d101299, d179466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16657 q = 1) (hb : d123120 q = 1) : d179636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d123120, d179636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16657, d123120, d179636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9791 q = 1) (hb : d101301 q = 1) : d179467 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101301, d179467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9791, d101301, d179467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d16658 q = 1) (hb : d123121 q = 1) : d179637 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d123121, d179637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16658, d123121, d179637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16659 q = 1) (hb : d123122 q = 1) : d179638 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d123122, d179638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16659, d123122, d179638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123122 q = 1) (hb : d178560 q = 1) : d179639 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178560, d179639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178560, d179639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123122 q = 1) (hb : d178561 q = 1) : d179640 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178561, d179640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178561, d179640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40580 (p : Pattern) (ha : d123132 p = 1) (hb : d178566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h3 (q : Pattern) (ha : d9800 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15005 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15005, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9802 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15006 q = 1) (hb : d123131 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15006, d123131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15007 q = 1) (hb : d123132 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15007, d123132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123132 q = 1) (hb : d178565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123132 q = 1) (hb : d178566 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40581 (p : Pattern) (ha : d177674 p = 1) (hb : d178576 p = 1) : d179662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177662 q = 1) (hb : d178562 q = 1) : d179641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177662, d178562, d179641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40578 q ha hb
    | true =>
      simp only [d177662, d178562, d179641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40579 q ha hb
  have h2 (q : Pattern) (ha : d177663 q = 1) (hb : d178563 q = 1) : d179642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177663, d178563, d179642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177663, d178563, d179642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177664 q = 1) (hb : d178564 q = 1) : d179643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177664, d178564, d179643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177664, d178564, d179643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177665 q = 1) (hb : d178567 q = 1) : d179644 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177665, d178567, d179644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40579 q ha hb
    | true =>
      simp only [d177665, d178567, d179644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40580 q ha hb
  have h5 (q : Pattern) (ha : d177666 q = 1) (hb : d178568 q = 1) : d179645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177666, d178568, d179645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177666, d178568, d179645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177667 q = 1) (hb : d178569 q = 1) : d179646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177667, d178569, d179646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177667, d178569, d179646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177668 q = 1) (hb : d178570 q = 1) : d179647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177668, d178570, d179647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177668, d178570, d179647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177665 q = 1) (hb : d178571 q = 1) : d179654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40579 q ha hb
    | true =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q ha hb
  have h9 (q : Pattern) (ha : d177666 q = 1) (hb : d178572 q = 1) : d179655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177667 q = 1) (hb : d178573 q = 1) : d179656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d160476 q = 1) (hb : d177669 q = 1) : d179657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q hb ha
    | true =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d160477 q = 1) (hb : d177670 q = 1) : d179658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d160478 q = 1) (hb : d177671 q = 1) : d179659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177672 q = 1) (hb : d178574 q = 1) : d179660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177673 q = 1) (hb : d178575 q = 1) : d179661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177673, d178575, d179661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177673, d178575, d179661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177674 q = 1) (hb : d178576 q = 1) : d179662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177674, d178576, d179662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177674, d178576, d179662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro40582 (p : Pattern) (ha : d177679 p = 1) (hb : d178580 p = 1) : d179667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177665 q = 1) (hb : d178571 q = 1) : d179654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40579 q ha hb
    | true =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q ha hb
  have h2 (q : Pattern) (ha : d177666 q = 1) (hb : d178572 q = 1) : d179655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177667 q = 1) (hb : d178573 q = 1) : d179656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160476 q = 1) (hb : d177669 q = 1) : d179657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q hb ha
    | true =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160477 q = 1) (hb : d177670 q = 1) : d179658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160478 q = 1) (hb : d177671 q = 1) : d179659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177672 q = 1) (hb : d178574 q = 1) : d179660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d160484 q = 1) (hb : d177677 q = 1) : d179665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160484, d177677, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d160484, d177677, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d177678 q = 1) (hb : d178579 q = 1) : d179666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177678, d178579, d179666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177678, d178579, d179666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177679 q = 1) (hb : d178580 q = 1) : d179667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177679, d178580, d179667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177679, d178580, d179667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40583 (p : Pattern) (ha : d177685 p = 1) (hb : d178586 p = 1) : d179673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177675 q = 1) (hb : d178577 q = 1) : d179663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177675, d178577, d179663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40581 q ha hb
    | true =>
      simp only [d177675, d178577, d179663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177676 q = 1) (hb : d178578 q = 1) : d179664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177676, d178578, d179664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177676, d178578, d179664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177680 q = 1) (hb : d178581 q = 1) : d179668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177680, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40582 q ha hb
    | true =>
      simp only [d177680, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177681 q = 1) (hb : d178582 q = 1) : d179669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177681, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177681, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177682 q = 1) (hb : d178583 q = 1) : d179670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177682, d178583, d179670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177682, d178583, d179670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177683 q = 1) (hb : d178584 q = 1) : d179671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177683, d178584, d179671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177683, d178584, d179671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177684 q = 1) (hb : d178585 q = 1) : d179672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177684, d178585, d179672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177684, d178585, d179672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177685 q = 1) (hb : d178586 q = 1) : d179673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177685, d178586, d179673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177685, d178586, d179673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40584 (p : Pattern) (ha : d177693 p = 1) (hb : d178590 p = 1) : d179681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177680 q = 1) (hb : d178581 q = 1) : d179668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177680, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40582 q ha hb
    | true =>
      simp only [d177680, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177681 q = 1) (hb : d178582 q = 1) : d179669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177681, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177681, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d160495 q = 1) (hb : d177688 q = 1) : d179676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d160495, d177688, d179676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40547 q ha hb
    | true =>
      simp only [d160495, d177688, d179676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d160496 q = 1) (hb : d177689 q = 1) : d179677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d160496, d177689, d179677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160496, d177689, d179677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177690 q = 1) (hb : d178587 q = 1) : d179678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177690, d178587, d179678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177690, d178587, d179678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177691 q = 1) (hb : d178588 q = 1) : d179679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177691, d178588, d179679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177691, d178588, d179679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177692 q = 1) (hb : d178589 q = 1) : d179680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177692, d178589, d179680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177692, d178589, d179680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177693 q = 1) (hb : d178590 q = 1) : d179681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177693, d178590, d179681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177693, d178590, d179681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40585 (p : Pattern) (ha : d177706 p = 1) (hb : d178580 p = 1) : d179667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177665 q = 1) (hb : d178571 q = 1) : d179654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40579 q ha hb
    | true =>
      simp only [d177665, d178571, d179654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q ha hb
  have h2 (q : Pattern) (ha : d177666 q = 1) (hb : d178572 q = 1) : d179655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177666, d178572, d179655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177667 q = 1) (hb : d178573 q = 1) : d179656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177667, d178573, d179656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160476 q = 1) (hb : d177669 q = 1) : d179657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q hb ha
    | true =>
      simp only [d160476, d177669, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160477 q = 1) (hb : d177670 q = 1) : d179658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160477, d177670, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160478 q = 1) (hb : d177671 q = 1) : d179659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160478, d177671, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177672 q = 1) (hb : d178574 q = 1) : d179660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177672, d178574, d179660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d160476 q = 1) (hb : d177701 q = 1) : d179657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d160476, d177701, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40546 q hb ha
    | true =>
      simp only [d160476, d177701, d179657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d160477 q = 1) (hb : d177702 q = 1) : d179658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d160477, d177702, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160477, d177702, d179658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d160478 q = 1) (hb : d177703 q = 1) : d179659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d160478, d177703, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160478, d177703, d179659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d160484 q = 1) (hb : d177704 q = 1) : d179665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d160484, d177704, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d160484, d177704, d179665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d177705 q = 1) (hb : d178579 q = 1) : d179666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177705, d178579, d179666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177705, d178579, d179666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177706 q = 1) (hb : d178580 q = 1) : d179667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177706, d178580, d179667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177706, d178580, d179667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40586 (p : Pattern) (ha : d177712 p = 1) (hb : d178596 p = 1) : d179687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177707 q = 1) (hb : d178581 q = 1) : d179668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177707, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40585 q ha hb
    | true =>
      simp only [d177707, d178581, d179668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177708 q = 1) (hb : d178582 q = 1) : d179669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177708, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177708, d178582, d179669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177709 q = 1) (hb : d178593 q = 1) : d179684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177709, d178593, d179684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177709, d178593, d179684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177710 q = 1) (hb : d178594 q = 1) : d179685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177710, d178594, d179685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177710, d178594, d179685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177711 q = 1) (hb : d178595 q = 1) : d179686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177711, d178595, d179686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177711, d178595, d179686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177712 q = 1) (hb : d178596 q = 1) : d179687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177712, d178596, d179687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177712, d178596, d179687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40587 (p : Pattern) (ha : d177718 p = 1) (hb : d178602 p = 1) : d179693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177694 q = 1) (hb : d178591 q = 1) : d179682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177694, d178591, d179682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40583 q ha hb
    | true =>
      simp only [d177694, d178591, d179682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40584 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177700 q = 1) (hb : d178592 q = 1) : d179683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177700, d178592, d179683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177700, d178592, d179683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177713 q = 1) (hb : d178597 q = 1) : d179688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177713, d178597, d179688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40586 q ha hb
    | true =>
      simp only [d177713, d178597, d179688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177714 q = 1) (hb : d178598 q = 1) : d179689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177714, d178598, d179689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177714, d178598, d179689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177715 q = 1) (hb : d178599 q = 1) : d179690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177715, d178599, d179690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177715, d178599, d179690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177716 q = 1) (hb : d178600 q = 1) : d179691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177716, d178600, d179691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177716, d178600, d179691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177717 q = 1) (hb : d178601 q = 1) : d179692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177717, d178601, d179692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177717, d178601, d179692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177718 q = 1) (hb : d178602 q = 1) : d179693 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177718, d178602, d179693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177718, d178602, d179693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40588 (p : Pattern) (ha : d177731 p = 1) (hb : d178608 p = 1) : d179710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177552 q = 1) (hb : d178470 q = 1) : d179514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177552, d178470, d179514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177552, d178470, d179514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40554 q ha hb
  have h2 (q : Pattern) (ha : d177553 q = 1) (hb : d178471 q = 1) : d179515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177553, d178471, d179515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177553, d178471, d179515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d177562 q = 1) (hb : d178479 q = 1) : d179524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177562, d178479, d179524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40554 q ha hb
    | true =>
      simp only [d177562, d178479, d179524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40556 q ha hb
  have h4 (q : Pattern) (ha : d177563 q = 1) (hb : d178480 q = 1) : d179525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177563, d178480, d179525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177563, d178480, d179525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177564 q = 1) (hb : d178481 q = 1) : d179526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177564, d178481, d179526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177564, d178481, d179526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177635 q = 1) (hb : d178544 q = 1) : d179602 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177635, d178544, d179602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40568 q ha hb
    | true =>
      simp only [d177635, d178544, d179602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40575 q ha hb
  have h7 (q : Pattern) (ha : d177648 q = 1) (hb : d178546 q = 1) : d179615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177648, d178546, d179615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40576 q ha hb
    | true =>
      simp only [d177648, d178546, d179615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40544 q hb ha
  have h8 (q : Pattern) (ha : d177649 q = 1) (hb : d178547 q = 1) : d179616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177649, d178547, d179616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177649, d178547, d179616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177650 q = 1) (hb : d178548 q = 1) : d179617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177650, d178548, d179617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177650, d178548, d179617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177651 q = 1) (hb : d178549 q = 1) : d179618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177651, d178549, d179618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177651, d178549, d179618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177655 q = 1) (hb : d178553 q = 1) : d179622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177655, d178553, d179622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177655, d178553, d179622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40577 q ha hb
  have h12 (q : Pattern) (ha : d160453 q = 1) (hb : d177657 q = 1) : d179624 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160453, d177657, d179624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160453, d177657, d179624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40545 q ha hb
  have h13 (q : Pattern) (ha : d177658 q = 1) (hb : d178554 q = 1) : d179625 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177658, d178554, d179625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177658, d178554, d179625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177659 q = 1) (hb : d178555 q = 1) : d179626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177659, d178555, d179626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177659, d178555, d179626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d177660 q = 1) (hb : d178556 q = 1) : d179627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177660, d178556, d179627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d177660, d178556, d179627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d177661 q = 1) (hb : d178557 q = 1) : d179628 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177661, d178557, d179628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177661, d178557, d179628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177719 q = 1) (hb : d178603 q = 1) : d179694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177719, d178603, d179694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177719, d178603, d179694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40587 q ha hb
  have h18 (q : Pattern) (ha : d160524 q = 1) (hb : d177726 q = 1) : d179705 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160524, d177726, d179705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160524, d177726, d179705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40549 q ha hb
  have h19 (q : Pattern) (ha : d177727 q = 1) (hb : d178604 q = 1) : d179706 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177727, d178604, d179706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177727, d178604, d179706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d177728 q = 1) (hb : d178605 q = 1) : d179707 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177728, d178605, d179707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177728, d178605, d179707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d177729 q = 1) (hb : d178606 q = 1) : d179708 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177729, d178606, d179708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d177729, d178606, d179708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d177730 q = 1) (hb : d178607 q = 1) : d179709 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177730, d178607, d179709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177730, d178607, d179709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177731 q = 1) (hb : d178608 q = 1) : d179710 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177731, d178608, d179710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177731, d178608, d179710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40589 (p : Pattern) (ha : d177737 p = 1) (hb : d178614 p = 1) : d179716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177732 q = 1) (hb : d178609 q = 1) : d179711 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177732, d178609, d179711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177732, d178609, d179711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40588 q ha hb
  have h2 (q : Pattern) (ha : d177733 q = 1) (hb : d178610 q = 1) : d179712 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177733, d178610, d179712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177733, d178610, d179712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177734 q = 1) (hb : d178611 q = 1) : d179713 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177734, d178611, d179713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177734, d178611, d179713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177735 q = 1) (hb : d178612 q = 1) : d179714 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177735, d178612, d179714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177735, d178612, d179714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177736 q = 1) (hb : d178613 q = 1) : d179715 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177736, d178613, d179715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177736, d178613, d179715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177737 q = 1) (hb : d178614 q = 1) : d179716 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177737, d178614, d179716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177737, d178614, d179716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40590 (p : Pattern) (ha : d10073 p = 1) (hb : d101489 p = 1) : d179723 p = 1 := by
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
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d1546 q = 1) (hb : d101478 q = 1) : d179720 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d101478, d179720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1546, d101478, d179720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1551 q = 1) : d1551 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1552 q = 1) (hb : d101479 q = 1) : d179721 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d101479, d179721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1552, d101479, d179721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1553 q = 1) (hb : d101480 q = 1) : d179722 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d101480, d179722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1553, d101480, d179722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h10 (q : Pattern) (ha : d10056 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10057 q = 1) (hb : d101484 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10058 q = 1) (hb : d101485 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10059 q = 1) (hb : d101486 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10060 q = 1) (hb : d101487 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10061 q = 1) (hb : d101488 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d10073 q = 1) (hb : d101489 q = 1) : d179723 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10073, d101489, d179723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10073, d101489, d179723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40591 (p : Pattern) (ha : d123237 p = 1) (hb : d178619 p = 1) : d179729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123237 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10074 q = 1) (hb : d101490 q = 1) : d179724 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101490, d179724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40590 q ha hb
    | true =>
      simp only [d10074, d101490, d179724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10076 q = 1) (hb : d101492 q = 1) : d179725 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101492, d179725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10076, d101492, d179725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16787 q = 1) (hb : d123236 q = 1) : d179726 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d123236, d179726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16787, d123236, d179726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16788 q = 1) (hb : d123237 q = 1) : d179727 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d123237, d179727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16788, d123237, d179727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123237 q = 1) (hb : d178618 q = 1) : d179728 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178618, d179728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178618, d179728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123237 q = 1) (hb : d178619 q = 1) : d179729 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178619, d179729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178619, d179729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40592 (p : Pattern) (ha : d1548 p = 1) (hb : d69209 p = 1) : d179730 p = 1 := by
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
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1519 q = 1) : d1519 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d1520 q = 1) (hb : d52502 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d52502, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1520, d52502, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1531 q = 1) : d1531 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d1532 q = 1) (hb : d69208 q = 1) : d43873 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1532, d69208, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1532, d69208, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
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
  have h12 (q : Pattern) (ha : d1548 q = 1) (hb : d69209 q = 1) : d179730 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1548, d69209, d179730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1548, d69209, d179730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro40593 (p : Pattern) (ha : d10114 p = 1) (hb : d101511 p = 1) : d179736 p = 1 := by
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
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1559 q = 1) : d1559 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d1560 q = 1) (hb : d101484 q = 1) : d179731 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d101484, d179731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40592 q ha hb
    | true =>
      simp only [d1560, d101484, d179731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1115 q = 1) : d1115 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1561 q = 1) (hb : d101485 q = 1) : d179732 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d101485, d179732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1561, d101485, d179732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1562 q = 1) (hb : d101507 q = 1) : d179733 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d101507, d179733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1562, d101507, d179733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d1565 q = 1) : d1565 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d1566 q = 1) (hb : d101508 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d101508, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1566, d101508, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1567 q = 1) (hb : d101509 q = 1) : d179734 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d101509, d179734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1567, d101509, d179734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1568 q = 1) (hb : d101510 q = 1) : d179735 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d101510, d179735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1568, d101510, d179735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h16 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
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
  have h19 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h21 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h23 (q : Pattern) (ha : d10114 q = 1) (hb : d101511 q = 1) : d179736 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10114, d101511, d179736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10114, d101511, d179736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40594 (p : Pattern) (ha : d123242 p = 1) (hb : d178621 p = 1) : d179742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10115 q = 1) (hb : d101512 q = 1) : d179737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101512, d179737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40593 q ha hb
    | true =>
      simp only [d10115, d101512, d179737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10117 q = 1) (hb : d101514 q = 1) : d179738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101514, d179738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10117, d101514, d179738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16792 q = 1) (hb : d123241 q = 1) : d179739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d123241, d179739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16792, d123241, d179739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16793 q = 1) (hb : d123242 q = 1) : d179740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d123242, d179740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16793, d123242, d179740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123242 q = 1) (hb : d178620 q = 1) : d179741 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178620, d179741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178620, d179741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123242 q = 1) (hb : d178621 q = 1) : d179742 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178621, d179742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178621, d179742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40595 (p : Pattern) (ha : d177750 p = 1) (hb : d178631 p = 1) : d179752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177741 q = 1) (hb : d178622 q = 1) : d179743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40591 q ha hb
    | true =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
  have h2 (q : Pattern) (ha : d177742 q = 1) (hb : d178623 q = 1) : d179744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177743 q = 1) (hb : d178624 q = 1) : d179745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177744 q = 1) (hb : d178625 q = 1) : d179746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
    | true =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177745 q = 1) (hb : d178626 q = 1) : d179747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177746 q = 1) (hb : d178627 q = 1) : d179748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177747 q = 1) (hb : d178628 q = 1) : d179749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177748 q = 1) (hb : d178629 q = 1) : d179750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177748, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177748, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177749 q = 1) (hb : d178630 q = 1) : d179751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177749, d178630, d179751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177749, d178630, d179751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177750 q = 1) (hb : d178631 q = 1) : d179752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177750, d178631, d179752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177750, d178631, d179752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40596 (p : Pattern) (ha : d177754 p = 1) (hb : d178635 p = 1) : d179756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177744 q = 1) (hb : d178625 q = 1) : d179746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
    | true =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d177745 q = 1) (hb : d178626 q = 1) : d179747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177746 q = 1) (hb : d178627 q = 1) : d179748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177748 q = 1) (hb : d178629 q = 1) : d179750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177748, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177748, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177753 q = 1) (hb : d178634 q = 1) : d179755 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177753, d178634, d179755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177753, d178634, d179755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177754 q = 1) (hb : d178635 q = 1) : d179756 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177754, d178635, d179756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177754, d178635, d179756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40597 (p : Pattern) (ha : d177760 p = 1) (hb : d178641 p = 1) : d179762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177758 q = 1) (hb : d178639 q = 1) : d179760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177759 q = 1) (hb : d178640 q = 1) : d179761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177759, d178640, d179761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177759, d178640, d179761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177760 q = 1) (hb : d178641 q = 1) : d179762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177760, d178641, d179762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177760, d178641, d179762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40598 (p : Pattern) (ha : d177764 p = 1) (hb : d178645 p = 1) : d179766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177762 q = 1) (hb : d178643 q = 1) : d179764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177763 q = 1) (hb : d178644 q = 1) : d179765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177763, d178644, d179765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177763, d178644, d179765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177764 q = 1) (hb : d178645 q = 1) : d179766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177764, d178645, d179766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177764, d178645, d179766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40599 (p : Pattern) (ha : d177770 p = 1) (hb : d178651 p = 1) : d179772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177765 q = 1) (hb : d178646 q = 1) : d179767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
    | true =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
  have h2 (q : Pattern) (ha : d177766 q = 1) (hb : d178647 q = 1) : d179768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177767 q = 1) (hb : d178648 q = 1) : d179769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177768 q = 1) (hb : d178649 q = 1) : d179770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177769 q = 1) (hb : d178650 q = 1) : d179771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177770 q = 1) (hb : d178651 q = 1) : d179772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177770, d178651, d179772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177770, d178651, d179772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40600 (p : Pattern) (ha : d177773 p = 1) (hb : d178654 p = 1) : d179775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177758 q = 1) (hb : d178639 q = 1) : d179760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177759 q = 1) (hb : d178640 q = 1) : d179761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177759, d178640, d179761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177759, d178640, d179761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177773 q = 1) (hb : d178654 q = 1) : d179775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177773, d178654, d179775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177773, d178654, d179775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40601 (p : Pattern) (ha : d177774 p = 1) (hb : d178655 p = 1) : d179776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177762 q = 1) (hb : d178643 q = 1) : d179764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177763 q = 1) (hb : d178644 q = 1) : d179765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177763, d178644, d179765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177763, d178644, d179765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177774 q = 1) (hb : d178655 q = 1) : d179776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177774, d178655, d179776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177774, d178655, d179776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40602 (p : Pattern) (ha : d177780 p = 1) (hb : d178661 p = 1) : d179782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177765 q = 1) (hb : d178646 q = 1) : d179767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
    | true =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
  have h2 (q : Pattern) (ha : d177766 q = 1) (hb : d178647 q = 1) : d179768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177767 q = 1) (hb : d178648 q = 1) : d179769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177768 q = 1) (hb : d178649 q = 1) : d179770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177769 q = 1) (hb : d178650 q = 1) : d179771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177775 q = 1) (hb : d178656 q = 1) : d179777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40600 q ha hb
    | true =>
      simp only [d177775, d178656, d179777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40601 q ha hb
  have h7 (q : Pattern) (ha : d177776 q = 1) (hb : d178657 q = 1) : d179778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177776, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177776, d178657, d179778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177777 q = 1) (hb : d178658 q = 1) : d179779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177777, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177777, d178658, d179779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177778 q = 1) (hb : d178659 q = 1) : d179780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177778, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177778, d178659, d179780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177779 q = 1) (hb : d178660 q = 1) : d179781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177779, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177779, d178660, d179781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177780 q = 1) (hb : d178661 q = 1) : d179782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177780, d178661, d179782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177780, d178661, d179782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40603 (p : Pattern) (ha : d177785 p = 1) (hb : d178666 p = 1) : d179787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177758 q = 1) (hb : d178639 q = 1) : d179760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177784 q = 1) (hb : d178665 q = 1) : d179786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177784, d178665, d179786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177784, d178665, d179786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177785 q = 1) (hb : d178666 q = 1) : d179787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177785, d178666, d179787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177785, d178666, d179787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40604 (p : Pattern) (ha : d177787 p = 1) (hb : d178668 p = 1) : d179789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177762 q = 1) (hb : d178643 q = 1) : d179764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177786 q = 1) (hb : d178667 q = 1) : d179788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177786, d178667, d179788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177786, d178667, d179788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177787 q = 1) (hb : d178668 q = 1) : d179789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177787, d178668, d179789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177787, d178668, d179789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40605 (p : Pattern) (ha : d177794 p = 1) (hb : d178675 p = 1) : d179796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177792 q = 1) (hb : d178673 q = 1) : d179794 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177792, d178673, d179794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177792, d178673, d179794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177793 q = 1) (hb : d178674 q = 1) : d179795 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177793, d178674, d179795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177793, d178674, d179795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177794 q = 1) (hb : d178675 q = 1) : d179796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177794, d178675, d179796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177794, d178675, d179796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40606 (p : Pattern) (ha : d177797 p = 1) (hb : d178678 p = 1) : d179799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177795 q = 1) (hb : d178676 q = 1) : d179797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177795, d178676, d179797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177795, d178676, d179797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177796 q = 1) (hb : d178677 q = 1) : d179798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177796, d178677, d179798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177796, d178677, d179798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177797 q = 1) (hb : d178678 q = 1) : d179799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177797, d178678, d179799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177797, d178678, d179799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40607 (p : Pattern) (ha : d123242 p = 1) (hb : d178688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15156 q = 1) (hb : d123241 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15156, d123241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15157 q = 1) (hb : d123242 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15157, d123242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123242 q = 1) (hb : d178687 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123242 q = 1) (hb : d178688 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40608 (p : Pattern) (ha : d10035 p = 1) (hb : d101472 p = 1) : d179806 p = 1 := by
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
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d1530 q = 1) (hb : d101469 q = 1) : d179803 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d101469, d179803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1530, d101469, d179803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d1536 q = 1) : d1536 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d1537 q = 1) (hb : d101470 q = 1) : d179804 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d101470, d179804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1537, d101470, d179804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1538 q = 1) (hb : d101471 q = 1) : d179805 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d101471, d179805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1538, d101471, d179805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10035 q = 1) (hb : d101472 q = 1) : d179806 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10035, d101472, d179806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10035, d101472, d179806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40609 (p : Pattern) (ha : d123315 p = 1) (hb : d178683 p = 1) : d179812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d101473 q = 1) : d179807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101473, d179807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40608 q ha hb
    | true =>
      simp only [d10036, d101473, d179807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10038 q = 1) (hb : d101475 q = 1) : d179808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101475, d179808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d101475, d179808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16859 q = 1) (hb : d123314 q = 1) : d179809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d123314, d179809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16859, d123314, d179809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16860 q = 1) (hb : d123315 q = 1) : d179810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d123315, d179810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16860, d123315, d179810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123315 q = 1) (hb : d178682 q = 1) : d179811 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178682, d179811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178682, d179811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123315 q = 1) (hb : d178683 q = 1) : d179812 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178683, d179812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178683, d179812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40610 (p : Pattern) (ha : d177806 p = 1) (hb : d178694 p = 1) : d179821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177801 q = 1) (hb : d178684 q = 1) : d179813 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177801, d178684, d179813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40609 q ha hb
    | true =>
      simp only [d177801, d178684, d179813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40591 q ha hb
  have h2 (q : Pattern) (ha : d177802 q = 1) (hb : d178685 q = 1) : d179814 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177802, d178685, d179814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177802, d178685, d179814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177803 q = 1) (hb : d178686 q = 1) : d179815 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177803, d178686, d179815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177803, d178686, d179815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177741 q = 1) (hb : d178689 q = 1) : d179816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177741, d178689, d179816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40591 q ha hb
    | true =>
      simp only [d177741, d178689, d179816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40607 q ha hb
  have h5 (q : Pattern) (ha : d177742 q = 1) (hb : d178690 q = 1) : d179817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177742, d178690, d179817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177742, d178690, d179817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177743 q = 1) (hb : d178691 q = 1) : d179818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177743, d178691, d179818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177743, d178691, d179818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177804 q = 1) (hb : d178692 q = 1) : d179819 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177804, d178692, d179819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177804, d178692, d179819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177741 q = 1) (hb : d178622 q = 1) : d179743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40591 q ha hb
    | true =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
  have h9 (q : Pattern) (ha : d177742 q = 1) (hb : d178623 q = 1) : d179744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177743 q = 1) (hb : d178624 q = 1) : d179745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177744 q = 1) (hb : d178625 q = 1) : d179746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
    | true =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d177745 q = 1) (hb : d178626 q = 1) : d179747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177746 q = 1) (hb : d178627 q = 1) : d179748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177747 q = 1) (hb : d178628 q = 1) : d179749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177805 q = 1) (hb : d178693 q = 1) : d179820 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177805, d178693, d179820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177805, d178693, d179820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177806 q = 1) (hb : d178694 q = 1) : d179821 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177806, d178694, d179821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177806, d178694, d179821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro40611 (p : Pattern) (ha : d177812 p = 1) (hb : d178700 p = 1) : d179827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177807 q = 1) (hb : d178695 q = 1) : d179822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177807, d178695, d179822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40610 q ha hb
    | true =>
      simp only [d177807, d178695, d179822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177808 q = 1) (hb : d178696 q = 1) : d179823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177808, d178696, d179823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177808, d178696, d179823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177809 q = 1) (hb : d178697 q = 1) : d179824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177809, d178697, d179824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177809, d178697, d179824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177810 q = 1) (hb : d178698 q = 1) : d179825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177810, d178698, d179825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177810, d178698, d179825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177811 q = 1) (hb : d178699 q = 1) : d179826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177811, d178699, d179826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177811, d178699, d179826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177812 q = 1) (hb : d178700 q = 1) : d179827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177812, d178700, d179827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177812, d178700, d179827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40612 (p : Pattern) (ha : d177820 p = 1) (hb : d178631 p = 1) : d179752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177741 q = 1) (hb : d178622 q = 1) : d179743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40591 q ha hb
    | true =>
      simp only [d177741, d178622, d179743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
  have h2 (q : Pattern) (ha : d177742 q = 1) (hb : d178623 q = 1) : d179744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177742, d178623, d179744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177743 q = 1) (hb : d178624 q = 1) : d179745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177743, d178624, d179745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177744 q = 1) (hb : d178625 q = 1) : d179746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
    | true =>
      simp only [d177744, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177745 q = 1) (hb : d178626 q = 1) : d179747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177745, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177746 q = 1) (hb : d178627 q = 1) : d179748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177746, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177747 q = 1) (hb : d178628 q = 1) : d179749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177747, d178628, d179749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177815 q = 1) (hb : d178625 q = 1) : d179746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177815, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40594 q ha hb
    | true =>
      simp only [d177815, d178625, d179746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177816 q = 1) (hb : d178626 q = 1) : d179747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177816, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177816, d178626, d179747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177817 q = 1) (hb : d178627 q = 1) : d179748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177817, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177817, d178627, d179748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d177818 q = 1) (hb : d178629 q = 1) : d179750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177818, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177818, d178629, d179750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177819 q = 1) (hb : d178630 q = 1) : d179751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177819, d178630, d179751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177819, d178630, d179751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177820 q = 1) (hb : d178631 q = 1) : d179752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177820, d178631, d179752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177820, d178631, d179752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40613 (p : Pattern) (ha : d177826 p = 1) (hb : d178706 p = 1) : d179833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177821 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177821, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40612 q ha hb
    | true =>
      simp only [d177821, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177822 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177822, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177822, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177823 q = 1) (hb : d178703 q = 1) : d179830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177823, d178703, d179830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177823, d178703, d179830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177824 q = 1) (hb : d178704 q = 1) : d179831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177824, d178704, d179831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177824, d178704, d179831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177825 q = 1) (hb : d178705 q = 1) : d179832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177825, d178705, d179832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177825, d178705, d179832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177826 q = 1) (hb : d178706 q = 1) : d179833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177826, d178706, d179833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177826, d178706, d179833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40614 (p : Pattern) (ha : d177832 p = 1) (hb : d178712 p = 1) : d179839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177788 q = 1) (hb : d178669 q = 1) : d179790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177788, d178669, d179790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40603 q ha hb
    | true =>
      simp only [d177788, d178669, d179790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40604 q ha hb
  have h2 (q : Pattern) (ha : d177789 q = 1) (hb : d178670 q = 1) : d179791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177789, d178670, d179791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177789, d178670, d179791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177790 q = 1) (hb : d178671 q = 1) : d179792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177790, d178671, d179792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177790, d178671, d179792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177791 q = 1) (hb : d178672 q = 1) : d179793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177791, d178672, d179793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177791, d178672, d179793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177798 q = 1) (hb : d178679 q = 1) : d179800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177798, d178679, d179800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40605 q ha hb
    | true =>
      simp only [d177798, d178679, d179800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40606 q ha hb
  have h6 (q : Pattern) (ha : d177799 q = 1) (hb : d178680 q = 1) : d179801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177799, d178680, d179801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177799, d178680, d179801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177800 q = 1) (hb : d178681 q = 1) : d179802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177800, d178681, d179802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177800, d178681, d179802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177813 q = 1) (hb : d178701 q = 1) : d179828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177813, d178701, d179828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40611 q ha hb
    | true =>
      simp only [d177813, d178701, d179828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177765 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177814 q = 1) (hb : d178702 q = 1) : d179829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177814, d178702, d179829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177814, d178702, d179829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177827 q = 1) (hb : d178707 q = 1) : d179834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177827, d178707, d179834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40613 q ha hb
    | true =>
      simp only [d177827, d178707, d179834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177828 q = 1) (hb : d178708 q = 1) : d179835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177828, d178708, d179835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177828, d178708, d179835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177829 q = 1) (hb : d178709 q = 1) : d179836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177829, d178709, d179836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177829, d178709, d179836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177830 q = 1) (hb : d178710 q = 1) : d179837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177830, d178710, d179837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177830, d178710, d179837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177831 q = 1) (hb : d178711 q = 1) : d179838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177831, d178711, d179838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177831, d178711, d179838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177832 q = 1) (hb : d178712 q = 1) : d179839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177832, d178712, d179839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177832, d178712, d179839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40615 (p : Pattern) (ha : d177833 p = 1) (hb : d178713 p = 1) : d179840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177758 q = 1) (hb : d178639 q = 1) : d179760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177758, d178639, d179760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177784 q = 1) (hb : d178665 q = 1) : d179786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177784, d178665, d179786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177784, d178665, d179786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177833 q = 1) (hb : d178713 q = 1) : d179840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177833, d178713, d179840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177833, d178713, d179840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40616 (p : Pattern) (ha : d177834 p = 1) (hb : d178714 p = 1) : d179841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177762 q = 1) (hb : d178643 q = 1) : d179764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177762, d178643, d179764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177786 q = 1) (hb : d178667 q = 1) : d179788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177786, d178667, d179788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177786, d178667, d179788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177834 q = 1) (hb : d178714 q = 1) : d179841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177834, d178714, d179841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177834, d178714, d179841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40617 (p : Pattern) (ha : d177839 p = 1) (hb : d178719 p = 1) : d179846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177757 q = 1) (hb : d178638 q = 1) : d179759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177757, d178638, d179759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177792 q = 1) (hb : d178673 q = 1) : d179794 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177792, d178673, d179794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177792, d178673, d179794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177793 q = 1) (hb : d178674 q = 1) : d179795 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177793, d178674, d179795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177793, d178674, d179795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177839 q = 1) (hb : d178719 q = 1) : d179846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177839, d178719, d179846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177839, d178719, d179846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40618 (p : Pattern) (ha : d177840 p = 1) (hb : d178720 p = 1) : d179847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177755 q = 1) (hb : d178636 q = 1) : d179757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40596 q ha hb
    | true =>
      simp only [d177755, d178636, d179757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177756 q = 1) (hb : d178637 q = 1) : d179758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177756, d178637, d179758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177761 q = 1) (hb : d178642 q = 1) : d179763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177761, d178642, d179763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177795 q = 1) (hb : d178676 q = 1) : d179797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177795, d178676, d179797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177795, d178676, d179797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177796 q = 1) (hb : d178677 q = 1) : d179798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177796, d178677, d179798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177796, d178677, d179798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177840 q = 1) (hb : d178720 q = 1) : d179847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177840, d178720, d179847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177840, d178720, d179847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40619 (p : Pattern) (ha : d177844 p = 1) (hb : d178724 p = 1) : d179851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177807 q = 1) (hb : d178695 q = 1) : d179822 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177807, d178695, d179822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40610 q ha hb
    | true =>
      simp only [d177807, d178695, d179822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177808 q = 1) (hb : d178696 q = 1) : d179823 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177808, d178696, d179823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177808, d178696, d179823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177751 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40595 q ha hb
    | true =>
      simp only [d177751, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177752 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177752, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177809 q = 1) (hb : d178697 q = 1) : d179824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177809, d178697, d179824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177809, d178697, d179824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177810 q = 1) (hb : d178698 q = 1) : d179825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177810, d178698, d179825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177810, d178698, d179825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177811 q = 1) (hb : d178699 q = 1) : d179826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177811, d178699, d179826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177811, d178699, d179826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177844 q = 1) (hb : d178724 q = 1) : d179851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177844, d178724, d179851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177844, d178724, d179851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40620 (p : Pattern) (ha : d177847 p = 1) (hb : d178727 p = 1) : d179854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177821 q = 1) (hb : d178632 q = 1) : d179753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177821, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40612 q ha hb
    | true =>
      simp only [d177821, d178632, d179753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177822 q = 1) (hb : d178633 q = 1) : d179754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177822, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177822, d178633, d179754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177823 q = 1) (hb : d178703 q = 1) : d179830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177823, d178703, d179830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177823, d178703, d179830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177824 q = 1) (hb : d178704 q = 1) : d179831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177824, d178704, d179831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177824, d178704, d179831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177825 q = 1) (hb : d178705 q = 1) : d179832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177825, d178705, d179832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177825, d178705, d179832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177847 q = 1) (hb : d178727 q = 1) : d179854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177847, d178727, d179854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177847, d178727, d179854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40621 (p : Pattern) (ha : d177853 p = 1) (hb : d178733 p = 1) : d179860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177788 q = 1) (hb : d178669 q = 1) : d179790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177788, d178669, d179790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40603 q ha hb
    | true =>
      simp only [d177788, d178669, d179790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40604 q ha hb
  have h2 (q : Pattern) (ha : d177789 q = 1) (hb : d178670 q = 1) : d179791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177789, d178670, d179791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177789, d178670, d179791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177790 q = 1) (hb : d178671 q = 1) : d179792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177790, d178671, d179792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177790, d178671, d179792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177791 q = 1) (hb : d178672 q = 1) : d179793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177791, d178672, d179793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177791, d178672, d179793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177798 q = 1) (hb : d178679 q = 1) : d179800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177798, d178679, d179800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40605 q ha hb
    | true =>
      simp only [d177798, d178679, d179800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40606 q ha hb
  have h6 (q : Pattern) (ha : d177799 q = 1) (hb : d178680 q = 1) : d179801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177799, d178680, d179801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177799, d178680, d179801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177800 q = 1) (hb : d178681 q = 1) : d179802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177800, d178681, d179802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177800, d178681, d179802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177813 q = 1) (hb : d178701 q = 1) : d179828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177813, d178701, d179828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40611 q ha hb
    | true =>
      simp only [d177813, d178701, d179828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177765 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d177814 q = 1) (hb : d178702 q = 1) : d179829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177814, d178702, d179829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177814, d178702, d179829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d177827 q = 1) (hb : d178707 q = 1) : d179834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177827, d178707, d179834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40613 q ha hb
    | true =>
      simp only [d177827, d178707, d179834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d177828 q = 1) (hb : d178708 q = 1) : d179835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177828, d178708, d179835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177828, d178708, d179835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177829 q = 1) (hb : d178709 q = 1) : d179836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177829, d178709, d179836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177829, d178709, d179836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177830 q = 1) (hb : d178710 q = 1) : d179837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177830, d178710, d179837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177830, d178710, d179837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177831 q = 1) (hb : d178711 q = 1) : d179838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177831, d178711, d179838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177831, d178711, d179838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177835 q = 1) (hb : d178715 q = 1) : d179842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177835, d178715, d179842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40615 q ha hb
    | true =>
      simp only [d177835, d178715, d179842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40616 q ha hb
  have h17 (q : Pattern) (ha : d177836 q = 1) (hb : d178716 q = 1) : d179843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177836, d178716, d179843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177836, d178716, d179843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177837 q = 1) (hb : d178717 q = 1) : d179844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177837, d178717, d179844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177837, d178717, d179844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d177838 q = 1) (hb : d178718 q = 1) : d179845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177838, d178718, d179845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177838, d178718, d179845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177841 q = 1) (hb : d178721 q = 1) : d179848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177841, d178721, d179848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40617 q ha hb
    | true =>
      simp only [d177841, d178721, d179848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40618 q ha hb
  have h21 (q : Pattern) (ha : d177842 q = 1) (hb : d178722 q = 1) : d179849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177842, d178722, d179849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177842, d178722, d179849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d177843 q = 1) (hb : d178723 q = 1) : d179850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177843, d178723, d179850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177843, d178723, d179850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177845 q = 1) (hb : d178725 q = 1) : d179852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177845, d178725, d179852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40619 q ha hb
    | true =>
      simp only [d177845, d178725, d179852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40600 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d177775 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d177846 q = 1) (hb : d178726 q = 1) : d179853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177846, d178726, d179853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d177846, d178726, d179853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d177848 q = 1) (hb : d178728 q = 1) : d179855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177848, d178728, d179855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40620 q ha hb
    | true =>
      simp only [d177848, d178728, d179855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d177849 q = 1) (hb : d178729 q = 1) : d179856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177849, d178729, d179856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d177849, d178729, d179856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d177850 q = 1) (hb : d178730 q = 1) : d179857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177850, d178730, d179857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d177850, d178730, d179857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d177851 q = 1) (hb : d178731 q = 1) : d179858 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177851, d178731, d179858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d177851, d178731, d179858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d177852 q = 1) (hb : d178732 q = 1) : d179859 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177852, d178732, d179859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177852, d178732, d179859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d177853 q = 1) (hb : d178733 q = 1) : d179860 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177853, d178733, d179860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d177853, d178733, d179860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40622 (p : Pattern) (ha : d177860 p = 1) (hb : d178740 p = 1) : d179867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177765 q = 1) (hb : d178646 q = 1) : d179767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40597 q ha hb
    | true =>
      simp only [d177765, d178646, d179767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
  have h2 (q : Pattern) (ha : d177766 q = 1) (hb : d178647 q = 1) : d179768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177766, d178647, d179768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177767 q = 1) (hb : d178648 q = 1) : d179769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177767, d178648, d179769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177768 q = 1) (hb : d178649 q = 1) : d179770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177768, d178649, d179770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177769 q = 1) (hb : d178650 q = 1) : d179771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177769, d178650, d179771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177855 q = 1) (hb : d178735 q = 1) : d179862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177855, d178735, d179862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
    | true =>
      simp only [d177855, d178735, d179862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177856 q = 1) (hb : d178736 q = 1) : d179863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177856, d178736, d179863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177856, d178736, d179863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177857 q = 1) (hb : d178737 q = 1) : d179864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177857, d178737, d179864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177857, d178737, d179864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177858 q = 1) (hb : d178738 q = 1) : d179865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177858, d178738, d179865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177858, d178738, d179865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177859 q = 1) (hb : d178739 q = 1) : d179866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177859, d178739, d179866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177859, d178739, d179866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177860 q = 1) (hb : d178740 q = 1) : d179867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177860, d178740, d179867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177860, d178740, d179867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40623 (p : Pattern) (ha : d177866 p = 1) (hb : d178746 p = 1) : d179873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177855 q = 1) (hb : d178735 q = 1) : d179862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177855, d178735, d179862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40598 q ha hb
    | true =>
      simp only [d177855, d178735, d179862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177856 q = 1) (hb : d178736 q = 1) : d179863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177856, d178736, d179863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177856, d178736, d179863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177857 q = 1) (hb : d178737 q = 1) : d179864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177857, d178737, d179864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177857, d178737, d179864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177858 q = 1) (hb : d178738 q = 1) : d179865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177858, d178738, d179865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177858, d178738, d179865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177859 q = 1) (hb : d178739 q = 1) : d179866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177859, d178739, d179866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177859, d178739, d179866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177861 q = 1) (hb : d178741 q = 1) : d179868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177861, d178741, d179868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40601 q ha hb
    | true =>
      simp only [d177861, d178741, d179868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177862 q = 1) (hb : d178742 q = 1) : d179869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177862, d178742, d179869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177862, d178742, d179869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177863 q = 1) (hb : d178743 q = 1) : d179870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177863, d178743, d179870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177863, d178743, d179870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177864 q = 1) (hb : d178744 q = 1) : d179871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177864, d178744, d179871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177864, d178744, d179871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177865 q = 1) (hb : d178745 q = 1) : d179872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177865, d178745, d179872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177865, d178745, d179872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177866 q = 1) (hb : d178746 q = 1) : d179873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177866, d178746, d179873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177866, d178746, d179873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40624 (p : Pattern) (ha : d177873 p = 1) (hb : d178753 p = 1) : d179880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177845 q = 1) (hb : d178725 q = 1) : d179852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177845, d178725, d179852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40619 q ha hb
    | true =>
      simp only [d177845, d178725, d179852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40600 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177846 q = 1) (hb : d178726 q = 1) : d179853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177846, d178726, d179853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177846, d178726, d179853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177848 q = 1) (hb : d178728 q = 1) : d179855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177848, d178728, d179855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40620 q ha hb
    | true =>
      simp only [d177848, d178728, d179855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177849 q = 1) (hb : d178729 q = 1) : d179856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177849, d178729, d179856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177849, d178729, d179856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177850 q = 1) (hb : d178730 q = 1) : d179857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177850, d178730, d179857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177850, d178730, d179857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177871 q = 1) (hb : d178751 q = 1) : d179878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177871, d178751, d179878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177871, d178751, d179878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177872 q = 1) (hb : d178752 q = 1) : d179879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177872, d178752, d179879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177872, d178752, d179879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177873 q = 1) (hb : d178753 q = 1) : d179880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177873, d178753, d179880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177873, d178753, d179880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40625 (p : Pattern) (ha : d177875 p = 1) (hb : d178755 p = 1) : d179882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177861 q = 1) (hb : d178741 q = 1) : d179868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177861, d178741, d179868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40601 q ha hb
    | true =>
      simp only [d177861, d178741, d179868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177862 q = 1) (hb : d178742 q = 1) : d179869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177862, d178742, d179869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177862, d178742, d179869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177863 q = 1) (hb : d178743 q = 1) : d179870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177863, d178743, d179870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177863, d178743, d179870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177864 q = 1) (hb : d178744 q = 1) : d179871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177864, d178744, d179871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177864, d178744, d179871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177865 q = 1) (hb : d178745 q = 1) : d179872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177865, d178745, d179872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177865, d178745, d179872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177875 q = 1) (hb : d178755 q = 1) : d179882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177875, d178755, d179882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177875, d178755, d179882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40626 (p : Pattern) (ha : d123422 p = 1) (hb : d178762 p = 1) : d179893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123422 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17004 q = 1) (hb : d123419 q = 1) : d179888 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d123419, d179888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17004, d123419, d179888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40608 q ha hb
  have h3 (q : Pattern) (ha : d10036 q = 1) (hb : d101473 q = 1) : d179807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101473, d179807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40608 q ha hb
    | true =>
      simp only [d10036, d101473, d179807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17005 q = 1) (hb : d123420 q = 1) : d179889 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d123420, d179889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17005, d123420, d179889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10038 q = 1) (hb : d101475 q = 1) : d179808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101475, d179808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10038, d101475, d179808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17006 q = 1) (hb : d123421 q = 1) : d179890 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d123421, d179890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17006, d123421, d179890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17007 q = 1) (hb : d123422 q = 1) : d179891 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d123422, d179891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17007, d123422, d179891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123422 q = 1) (hb : d178761 q = 1) : d179892 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178761, d179892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178761, d179892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123422 q = 1) (hb : d178762 q = 1) : d179893 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178762, d179893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178762, d179893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40627 (p : Pattern) (ha : d123429 p = 1) (hb : d178764 p = 1) : d179899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17011 q = 1) (hb : d123426 q = 1) : d179894 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d123426, d179894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17011, d123426, d179894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40590 q ha hb
  have h3 (q : Pattern) (ha : d10074 q = 1) (hb : d101490 q = 1) : d179724 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101490, d179724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40590 q ha hb
    | true =>
      simp only [d10074, d101490, d179724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17012 q = 1) (hb : d123427 q = 1) : d179895 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d123427, d179895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17012, d123427, d179895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10076 q = 1) (hb : d101492 q = 1) : d179725 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101492, d179725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10076, d101492, d179725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17013 q = 1) (hb : d123428 q = 1) : d179896 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d123428, d179896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17013, d123428, d179896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17014 q = 1) (hb : d123429 q = 1) : d179897 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d123429, d179897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17014, d123429, d179897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123429 q = 1) (hb : d178763 q = 1) : d179898 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178763, d179898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178763, d179898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123429 q = 1) (hb : d178764 q = 1) : d179899 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178764, d179899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178764, d179899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40628 (p : Pattern) (ha : d123439 p = 1) (hb : d178769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h3 (q : Pattern) (ha : d10085 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15398 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10087 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15399 q = 1) (hb : d123438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15400 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15400, d123439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123439 q = 1) (hb : d178768 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123439 q = 1) (hb : d178769 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40629 (p : Pattern) (ha : d123439 p = 1) (hb : d178775 p = 1) : d179912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123439 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17027 q = 1) (hb : d123436 q = 1) : d179907 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d123436, d179907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17027, d123436, d179907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40593 q ha hb
  have h3 (q : Pattern) (ha : d10115 q = 1) (hb : d101512 q = 1) : d179737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101512, d179737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40593 q ha hb
    | true =>
      simp only [d10115, d101512, d179737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17028 q = 1) (hb : d123437 q = 1) : d179908 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d123437, d179908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17028, d123437, d179908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10117 q = 1) (hb : d101514 q = 1) : d179738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101514, d179738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10117, d101514, d179738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17029 q = 1) (hb : d123438 q = 1) : d179909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d123438, d179909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17029, d123438, d179909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17030 q = 1) (hb : d123439 q = 1) : d179910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d123439, d179910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17030, d123439, d179910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123439 q = 1) (hb : d178774 q = 1) : d179911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178774, d179911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178774, d179911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123439 q = 1) (hb : d178775 q = 1) : d179912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178775, d179912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178775, d179912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40630 (p : Pattern) (ha : d177893 p = 1) (hb : d178784 p = 1) : d179921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177881 q = 1) (hb : d178765 q = 1) : d179900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177881, d178765, d179900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40626 q ha hb
    | true =>
      simp only [d177881, d178765, d179900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40627 q ha hb
  have h2 (q : Pattern) (ha : d177882 q = 1) (hb : d178766 q = 1) : d179901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177882, d178766, d179901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177882, d178766, d179901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177883 q = 1) (hb : d178767 q = 1) : d179902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177883, d178767, d179902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177883, d178767, d179902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177884 q = 1) (hb : d178770 q = 1) : d179903 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177884, d178770, d179903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40627 q ha hb
    | true =>
      simp only [d177884, d178770, d179903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40628 q ha hb
  have h5 (q : Pattern) (ha : d177885 q = 1) (hb : d178771 q = 1) : d179904 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177885, d178771, d179904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177885, d178771, d179904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177886 q = 1) (hb : d178772 q = 1) : d179905 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177886, d178772, d179905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177886, d178772, d179905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177887 q = 1) (hb : d178773 q = 1) : d179906 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177887, d178773, d179906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177887, d178773, d179906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177884 q = 1) (hb : d178776 q = 1) : d179913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40627 q ha hb
    | true =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
  have h9 (q : Pattern) (ha : d177885 q = 1) (hb : d178777 q = 1) : d179914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177886 q = 1) (hb : d178778 q = 1) : d179915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177888 q = 1) (hb : d178779 q = 1) : d179916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
    | true =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d177889 q = 1) (hb : d178780 q = 1) : d179917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177890 q = 1) (hb : d178781 q = 1) : d179918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177891 q = 1) (hb : d178782 q = 1) : d179919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177892 q = 1) (hb : d178783 q = 1) : d179920 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177892, d178783, d179920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177892, d178783, d179920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177893 q = 1) (hb : d178784 q = 1) : d179921 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177893, d178784, d179921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177893, d178784, d179921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro40631 (p : Pattern) (ha : d177898 p = 1) (hb : d178789 p = 1) : d179926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177884 q = 1) (hb : d178776 q = 1) : d179913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40627 q ha hb
    | true =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
  have h2 (q : Pattern) (ha : d177885 q = 1) (hb : d178777 q = 1) : d179914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177886 q = 1) (hb : d178778 q = 1) : d179915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177888 q = 1) (hb : d178779 q = 1) : d179916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
    | true =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177889 q = 1) (hb : d178780 q = 1) : d179917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177890 q = 1) (hb : d178781 q = 1) : d179918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177891 q = 1) (hb : d178782 q = 1) : d179919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177896 q = 1) (hb : d178787 q = 1) : d179924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177896, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177896, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177897 q = 1) (hb : d178788 q = 1) : d179925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177897, d178788, d179925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177897, d178788, d179925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177898 q = 1) (hb : d178789 q = 1) : d179926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177898, d178789, d179926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177898, d178789, d179926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40632 (p : Pattern) (ha : d177904 p = 1) (hb : d178795 p = 1) : d179932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177894 q = 1) (hb : d178785 q = 1) : d179922 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177894, d178785, d179922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40630 q ha hb
    | true =>
      simp only [d177894, d178785, d179922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177895 q = 1) (hb : d178786 q = 1) : d179923 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177895, d178786, d179923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177895, d178786, d179923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177899 q = 1) (hb : d178790 q = 1) : d179927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177899, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40631 q ha hb
    | true =>
      simp only [d177899, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177900 q = 1) (hb : d178791 q = 1) : d179928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177900, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177900, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177901 q = 1) (hb : d178792 q = 1) : d179929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177901, d178792, d179929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177901, d178792, d179929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177902 q = 1) (hb : d178793 q = 1) : d179930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177902, d178793, d179930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177902, d178793, d179930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177903 q = 1) (hb : d178794 q = 1) : d179931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177903, d178794, d179931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177903, d178794, d179931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177904 q = 1) (hb : d178795 q = 1) : d179932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177904, d178795, d179932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177904, d178795, d179932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40633 (p : Pattern) (ha : d177906 p = 1) (hb : d178797 p = 1) : d179934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177888 q = 1) (hb : d178779 q = 1) : d179916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
    | true =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d177889 q = 1) (hb : d178780 q = 1) : d179917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177890 q = 1) (hb : d178781 q = 1) : d179918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177896 q = 1) (hb : d178787 q = 1) : d179924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177896, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177896, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177905 q = 1) (hb : d178796 q = 1) : d179933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177905, d178796, d179933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177905, d178796, d179933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177906 q = 1) (hb : d178797 q = 1) : d179934 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177906, d178797, d179934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177906, d178797, d179934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40634 (p : Pattern) (ha : d177912 p = 1) (hb : d178803 p = 1) : d179940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177899 q = 1) (hb : d178790 q = 1) : d179927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177899, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40631 q ha hb
    | true =>
      simp only [d177899, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177900 q = 1) (hb : d178791 q = 1) : d179928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177900, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177900, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177907 q = 1) (hb : d178798 q = 1) : d179935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177907, d178798, d179935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40633 q ha hb
    | true =>
      simp only [d177907, d178798, d179935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177908 q = 1) (hb : d178799 q = 1) : d179936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177908, d178799, d179936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177908, d178799, d179936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177909 q = 1) (hb : d178800 q = 1) : d179937 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177909, d178800, d179937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177909, d178800, d179937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177910 q = 1) (hb : d178801 q = 1) : d179938 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177910, d178801, d179938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177910, d178801, d179938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177911 q = 1) (hb : d178802 q = 1) : d179939 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177911, d178802, d179939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177911, d178802, d179939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177912 q = 1) (hb : d178803 q = 1) : d179940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177912, d178803, d179940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177912, d178803, d179940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40635 (p : Pattern) (ha : d177925 p = 1) (hb : d178789 p = 1) : d179926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177884 q = 1) (hb : d178776 q = 1) : d179913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40627 q ha hb
    | true =>
      simp only [d177884, d178776, d179913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
  have h2 (q : Pattern) (ha : d177885 q = 1) (hb : d178777 q = 1) : d179914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177885, d178777, d179914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177886 q = 1) (hb : d178778 q = 1) : d179915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177886, d178778, d179915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177888 q = 1) (hb : d178779 q = 1) : d179916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
    | true =>
      simp only [d177888, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177889 q = 1) (hb : d178780 q = 1) : d179917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177889, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177890 q = 1) (hb : d178781 q = 1) : d179918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177890, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177891 q = 1) (hb : d178782 q = 1) : d179919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177891, d178782, d179919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177920 q = 1) (hb : d178779 q = 1) : d179916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177920, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40629 q ha hb
    | true =>
      simp only [d177920, d178779, d179916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177921 q = 1) (hb : d178780 q = 1) : d179917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177921, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177921, d178780, d179917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177922 q = 1) (hb : d178781 q = 1) : d179918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177922, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177922, d178781, d179918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d177923 q = 1) (hb : d178787 q = 1) : d179924 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177923, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177923, d178787, d179924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d177924 q = 1) (hb : d178788 q = 1) : d179925 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177924, d178788, d179925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177924, d178788, d179925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177925 q = 1) (hb : d178789 q = 1) : d179926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177925, d178789, d179926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177925, d178789, d179926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40636 (p : Pattern) (ha : d177931 p = 1) (hb : d178809 p = 1) : d179946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177926 q = 1) (hb : d178790 q = 1) : d179927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177926, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40635 q ha hb
    | true =>
      simp only [d177926, d178790, d179927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177927 q = 1) (hb : d178791 q = 1) : d179928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177927, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177927, d178791, d179928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177928 q = 1) (hb : d178806 q = 1) : d179943 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177928, d178806, d179943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177928, d178806, d179943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177929 q = 1) (hb : d178807 q = 1) : d179944 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177929, d178807, d179944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177929, d178807, d179944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177930 q = 1) (hb : d178808 q = 1) : d179945 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177930, d178808, d179945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177930, d178808, d179945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177931 q = 1) (hb : d178809 q = 1) : d179946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177931, d178809, d179946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177931, d178809, d179946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40637 (p : Pattern) (ha : d177937 p = 1) (hb : d178815 p = 1) : d179952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177913 q = 1) (hb : d178804 q = 1) : d179941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177913, d178804, d179941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40632 q ha hb
    | true =>
      simp only [d177913, d178804, d179941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177919 q = 1) (hb : d178805 q = 1) : d179942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177919, d178805, d179942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177919, d178805, d179942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d177932 q = 1) (hb : d178810 q = 1) : d179947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177932, d178810, d179947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40636 q ha hb
    | true =>
      simp only [d177932, d178810, d179947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177933 q = 1) (hb : d178811 q = 1) : d179948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177933, d178811, d179948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177933, d178811, d179948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177934 q = 1) (hb : d178812 q = 1) : d179949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177934, d178812, d179949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177934, d178812, d179949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177935 q = 1) (hb : d178813 q = 1) : d179950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177935, d178813, d179950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177935, d178813, d179950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177936 q = 1) (hb : d178814 q = 1) : d179951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177936, d178814, d179951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177936, d178814, d179951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177937 q = 1) (hb : d178815 q = 1) : d179952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177937, d178815, d179952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177937, d178815, d179952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40638 (p : Pattern) (ha : d177917 p = 1) (hb : d178820 p = 1) : d179957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177907 q = 1) (hb : d178798 q = 1) : d179935 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177907, d178798, d179935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40633 q ha hb
    | true =>
      simp only [d177907, d178798, d179935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177908 q = 1) (hb : d178799 q = 1) : d179936 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177908, d178799, d179936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177908, d178799, d179936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177914 q = 1) (hb : d178817 q = 1) : d179954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177914, d178817, d179954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177914, d178817, d179954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177915 q = 1) (hb : d178818 q = 1) : d179955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177915, d178818, d179955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177915, d178818, d179955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177916 q = 1) (hb : d178819 q = 1) : d179956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177916, d178819, d179956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177916, d178819, d179956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177917 q = 1) (hb : d178820 q = 1) : d179957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177917, d178820, d179957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177917, d178820, d179957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40639 (p : Pattern) (ha : d177944 p = 1) (hb : d178826 p = 1) : d179963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177939 q = 1) (hb : d178821 q = 1) : d179958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177939, d178821, d179958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40638 q ha hb
    | true =>
      simp only [d177939, d178821, d179958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177940 q = 1) (hb : d178822 q = 1) : d179959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177940, d178822, d179959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177940, d178822, d179959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177941 q = 1) (hb : d178823 q = 1) : d179960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177941, d178823, d179960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177941, d178823, d179960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177942 q = 1) (hb : d178824 q = 1) : d179961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177942, d178824, d179961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177942, d178824, d179961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177943 q = 1) (hb : d178825 q = 1) : d179962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177943, d178825, d179962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177943, d178825, d179962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177944 q = 1) (hb : d178826 q = 1) : d179963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177944, d178826, d179963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177944, d178826, d179963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40640 (p : Pattern) (ha : d177950 p = 1) (hb : d178832 p = 1) : d179969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177771 q = 1) (hb : d178652 q = 1) : d179773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177771, d178652, d179773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177771, d178652, d179773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40599 q ha hb
  have h2 (q : Pattern) (ha : d177772 q = 1) (hb : d178653 q = 1) : d179774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177772, d178653, d179774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177772, d178653, d179774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d177781 q = 1) (hb : d178662 q = 1) : d179783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177781, d178662, d179783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40599 q ha hb
    | true =>
      simp only [d177781, d178662, d179783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40602 q ha hb
  have h4 (q : Pattern) (ha : d177782 q = 1) (hb : d178663 q = 1) : d179784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177782, d178663, d179784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177782, d178663, d179784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177783 q = 1) (hb : d178664 q = 1) : d179785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177783, d178664, d179785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177783, d178664, d179785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177854 q = 1) (hb : d178734 q = 1) : d179861 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177854, d178734, d179861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40614 q ha hb
    | true =>
      simp only [d177854, d178734, d179861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40621 q ha hb
  have h7 (q : Pattern) (ha : d177867 q = 1) (hb : d178747 q = 1) : d179874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177867, d178747, d179874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40622 q ha hb
    | true =>
      simp only [d177867, d178747, d179874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40623 q ha hb
  have h8 (q : Pattern) (ha : d177868 q = 1) (hb : d178748 q = 1) : d179875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177868, d178748, d179875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177868, d178748, d179875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177869 q = 1) (hb : d178749 q = 1) : d179876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177869, d178749, d179876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177869, d178749, d179876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177870 q = 1) (hb : d178750 q = 1) : d179877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177870, d178750, d179877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177870, d178750, d179877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177874 q = 1) (hb : d178754 q = 1) : d179881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177874, d178754, d179881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177874, d178754, d179881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40624 q ha hb
  have h12 (q : Pattern) (ha : d177876 q = 1) (hb : d178756 q = 1) : d179883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177876, d178756, d179883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177876, d178756, d179883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40625 q ha hb
  have h13 (q : Pattern) (ha : d177877 q = 1) (hb : d178757 q = 1) : d179884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177877, d178757, d179884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177877, d178757, d179884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d177878 q = 1) (hb : d178758 q = 1) : d179885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177878, d178758, d179885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177878, d178758, d179885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d177879 q = 1) (hb : d178759 q = 1) : d179886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177879, d178759, d179886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d177879, d178759, d179886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d177880 q = 1) (hb : d178760 q = 1) : d179887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177880, d178760, d179887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177880, d178760, d179887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177938 q = 1) (hb : d178816 q = 1) : d179953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177938, d178816, d179953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177938, d178816, d179953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40637 q ha hb
  have h18 (q : Pattern) (ha : d177945 q = 1) (hb : d178827 q = 1) : d179964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177945, d178827, d179964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177945, d178827, d179964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40639 q ha hb
  have h19 (q : Pattern) (ha : d177946 q = 1) (hb : d178828 q = 1) : d179965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177946, d178828, d179965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d177946, d178828, d179965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d177947 q = 1) (hb : d178829 q = 1) : d179966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177947, d178829, d179966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d177947, d178829, d179966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d177948 q = 1) (hb : d178830 q = 1) : d179967 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177948, d178830, d179967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d177948, d178830, d179967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d177949 q = 1) (hb : d178831 q = 1) : d179968 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177949, d178831, d179968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d177949, d178831, d179968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d177950 q = 1) (hb : d178832 q = 1) : d179969 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177950, d178832, d179969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d177950, d178832, d179969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40641 (p : Pattern) (ha : d177956 p = 1) (hb : d178838 p = 1) : d179975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177951 q = 1) (hb : d178833 q = 1) : d179970 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177951, d178833, d179970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177951, d178833, d179970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40640 q ha hb
  have h2 (q : Pattern) (ha : d177952 q = 1) (hb : d178834 q = 1) : d179971 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177952, d178834, d179971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177952, d178834, d179971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177953 q = 1) (hb : d178835 q = 1) : d179972 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177953, d178835, d179972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177953, d178835, d179972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177954 q = 1) (hb : d178836 q = 1) : d179973 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177954, d178836, d179973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177954, d178836, d179973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177955 q = 1) (hb : d178837 q = 1) : d179974 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177955, d178837, d179974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177955, d178837, d179974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177956 q = 1) (hb : d178838 q = 1) : d179975 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177956, d178838, d179975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177956, d178838, d179975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40642 (p : Pattern) (ha : d10363 p = 1) (hb : d101673 p = 1) : d179983 p = 1 := by
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
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d2026 q = 1) (hb : d101670 q = 1) : d179980 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d101670, d179980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2026, d101670, d179980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2031 q = 1) : d2031 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2032 q = 1) (hb : d101671 q = 1) : d179981 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d101671, d179981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2032, d101671, d179981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2033 q = 1) (hb : d101672 q = 1) : d179982 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d101672, d179982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2033, d101672, d179982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d10363 q = 1) (hb : d101673 q = 1) : d179983 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10363, d101673, d179983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10363, d101673, d179983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h9 p ha hb
theorem andIntro40643 (p : Pattern) (ha : d113866 p = 1) (hb : d178844 p = 1) : d179989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d101674 q = 1) : d179984 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101674, d179984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40642 q ha hb
    | true =>
      simp only [d10364, d101674, d179984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10366 q = 1) (hb : d101676 q = 1) : d179985 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101676, d179985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d101676, d179985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17153 q = 1) (hb : d113865 q = 1) : d179986 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d113865, d179986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17153, d113865, d179986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17154 q = 1) (hb : d113866 q = 1) : d179987 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d113866, d179987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17154, d113866, d179987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d113866 q = 1) (hb : d178843 q = 1) : d179988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178843, d179988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178843, d179988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113866 q = 1) (hb : d178844 q = 1) : d179989 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178844, d179989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178844, d179989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40644 (p : Pattern) (ha : d10390 p = 1) (hb : d101691 p = 1) : d179993 p = 1 := by
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
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d2044 q = 1) : d2044 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d2045 q = 1) (hb : d74441 q = 1) : d179990 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d74441, d179990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d74441, d179990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2049 q = 1) : d2049 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d2050 q = 1) (hb : d74442 q = 1) : d179991 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d74442, d179991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2050, d74442, d179991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2051 q = 1) (hb : d74443 q = 1) : d179992 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d74443, d179992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2051, d74443, d179992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h17 (q : Pattern) (ha : d10390 q = 1) (hb : d101691 q = 1) : d179993 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10390, d101691, d179993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10390, d101691, d179993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro40645 (p : Pattern) (ha : d123548 p = 1) (hb : d178846 p = 1) : d179999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10391 q = 1) (hb : d101692 q = 1) : d179994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101692, d179994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40644 q ha hb
    | true =>
      simp only [d10391, d101692, d179994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10393 q = 1) (hb : d101694 q = 1) : d179995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101694, d179995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10393, d101694, d179995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17158 q = 1) (hb : d123547 q = 1) : d179996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d123547, d179996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17158, d123547, d179996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17159 q = 1) (hb : d123548 q = 1) : d179997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, d123548, d179997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17159, d123548, d179997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123548 q = 1) (hb : d178845 q = 1) : d179998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178845, d179998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178845, d179998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123548 q = 1) (hb : d178846 q = 1) : d179999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178846, d179999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178846, d179999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40646 (p : Pattern) (ha : d177970 p = 1) (hb : d178856 p = 1) : d180009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177961 q = 1) (hb : d178847 q = 1) : d180000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40643 q ha hb
    | true =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
  have h2 (q : Pattern) (ha : d177962 q = 1) (hb : d178848 q = 1) : d180001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177963 q = 1) (hb : d178849 q = 1) : d180002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177964 q = 1) (hb : d178850 q = 1) : d180003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
    | true =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177965 q = 1) (hb : d178851 q = 1) : d180004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177966 q = 1) (hb : d178852 q = 1) : d180005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177967 q = 1) (hb : d178853 q = 1) : d180006 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177968 q = 1) (hb : d178854 q = 1) : d180007 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177968, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177968, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d177969 q = 1) (hb : d178855 q = 1) : d180008 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177969, d178855, d180008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177969, d178855, d180008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177970 q = 1) (hb : d178856 q = 1) : d180009 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177970, d178856, d180009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d177970, d178856, d180009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40647 (p : Pattern) (ha : d177974 p = 1) (hb : d178860 p = 1) : d180013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177964 q = 1) (hb : d178850 q = 1) : d180003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
    | true =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d177965 q = 1) (hb : d178851 q = 1) : d180004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177966 q = 1) (hb : d178852 q = 1) : d180005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177968 q = 1) (hb : d178854 q = 1) : d180007 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177968, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177968, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177973 q = 1) (hb : d178859 q = 1) : d180012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177973, d178859, d180012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177973, d178859, d180012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177974 q = 1) (hb : d178860 q = 1) : d180013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177974, d178860, d180013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177974, d178860, d180013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40648 (p : Pattern) (ha : d177980 p = 1) (hb : d178866 p = 1) : d180019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177978 q = 1) (hb : d178864 q = 1) : d180017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177979 q = 1) (hb : d178865 q = 1) : d180018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177979, d178865, d180018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177979, d178865, d180018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177980 q = 1) (hb : d178866 q = 1) : d180019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177980, d178866, d180019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177980, d178866, d180019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40649 (p : Pattern) (ha : d177984 p = 1) (hb : d178870 p = 1) : d180023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177982 q = 1) (hb : d178868 q = 1) : d180021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177983 q = 1) (hb : d178869 q = 1) : d180022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177983, d178869, d180022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177983, d178869, d180022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177984 q = 1) (hb : d178870 q = 1) : d180023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177984, d178870, d180023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177984, d178870, d180023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40650 (p : Pattern) (ha : d177990 p = 1) (hb : d178876 p = 1) : d180029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177985 q = 1) (hb : d178871 q = 1) : d180024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
    | true =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
  have h2 (q : Pattern) (ha : d177986 q = 1) (hb : d178872 q = 1) : d180025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177987 q = 1) (hb : d178873 q = 1) : d180026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177988 q = 1) (hb : d178874 q = 1) : d180027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177989 q = 1) (hb : d178875 q = 1) : d180028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177990 q = 1) (hb : d178876 q = 1) : d180029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177990, d178876, d180029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177990, d178876, d180029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40651 (p : Pattern) (ha : d177993 p = 1) (hb : d178879 p = 1) : d180032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177978 q = 1) (hb : d178864 q = 1) : d180017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d177979 q = 1) (hb : d178865 q = 1) : d180018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177979, d178865, d180018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177979, d178865, d180018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d177993 q = 1) (hb : d178879 q = 1) : d180032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177993, d178879, d180032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177993, d178879, d180032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40652 (p : Pattern) (ha : d177994 p = 1) (hb : d178880 p = 1) : d180033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177982 q = 1) (hb : d178868 q = 1) : d180021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d177983 q = 1) (hb : d178869 q = 1) : d180022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177983, d178869, d180022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177983, d178869, d180022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d177994 q = 1) (hb : d178880 q = 1) : d180033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177994, d178880, d180033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177994, d178880, d180033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40653 (p : Pattern) (ha : d178000 p = 1) (hb : d178886 p = 1) : d180039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177985 q = 1) (hb : d178871 q = 1) : d180024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
    | true =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
  have h2 (q : Pattern) (ha : d177986 q = 1) (hb : d178872 q = 1) : d180025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177987 q = 1) (hb : d178873 q = 1) : d180026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177988 q = 1) (hb : d178874 q = 1) : d180027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177989 q = 1) (hb : d178875 q = 1) : d180028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177995 q = 1) (hb : d178881 q = 1) : d180034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40651 q ha hb
    | true =>
      simp only [d177995, d178881, d180034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40652 q ha hb
  have h7 (q : Pattern) (ha : d177996 q = 1) (hb : d178882 q = 1) : d180035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177996, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177996, d178882, d180035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177997 q = 1) (hb : d178883 q = 1) : d180036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177997, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d177997, d178883, d180036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d177998 q = 1) (hb : d178884 q = 1) : d180037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177998, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177998, d178884, d180037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177999 q = 1) (hb : d178885 q = 1) : d180038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177999, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177999, d178885, d180038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178000 q = 1) (hb : d178886 q = 1) : d180039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178000, d178886, d180039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178000, d178886, d180039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40654 (p : Pattern) (ha : d178005 p = 1) (hb : d178891 p = 1) : d180044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177978 q = 1) (hb : d178864 q = 1) : d180017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178004 q = 1) (hb : d178890 q = 1) : d180043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178004, d178890, d180043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178004, d178890, d180043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178005 q = 1) (hb : d178891 q = 1) : d180044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178005, d178891, d180044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178005, d178891, d180044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40655 (p : Pattern) (ha : d178007 p = 1) (hb : d178893 p = 1) : d180046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177982 q = 1) (hb : d178868 q = 1) : d180021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178006 q = 1) (hb : d178892 q = 1) : d180045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178006, d178892, d180045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178006, d178892, d180045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178007 q = 1) (hb : d178893 q = 1) : d180046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178007, d178893, d180046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178007, d178893, d180046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40656 (p : Pattern) (ha : d178014 p = 1) (hb : d178900 p = 1) : d180053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178012 q = 1) (hb : d178898 q = 1) : d180051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178012, d178898, d180051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178012, d178898, d180051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178013 q = 1) (hb : d178899 q = 1) : d180052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178013, d178899, d180052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178013, d178899, d180052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178014 q = 1) (hb : d178900 q = 1) : d180053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178014, d178900, d180053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178014, d178900, d180053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40657 (p : Pattern) (ha : d178017 p = 1) (hb : d178903 p = 1) : d180056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178015 q = 1) (hb : d178901 q = 1) : d180054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178015, d178901, d180054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178015, d178901, d180054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178016 q = 1) (hb : d178902 q = 1) : d180055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178016, d178902, d180055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178016, d178902, d180055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178017 q = 1) (hb : d178903 q = 1) : d180056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178017, d178903, d180056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178017, d178903, d180056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40658 (p : Pattern) (ha : d123548 p = 1) (hb : d178911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d123547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d123548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d123548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d123548 q = 1) (hb : d178910 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d123548 q = 1) (hb : d178911 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40659 (p : Pattern) (ha : d178026 p = 1) (hb : d178917 p = 1) : d180068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d149593 q = 1) : d149593 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d178021 q = 1) (hb : d178907 q = 1) : d180060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178021, d178907, d180060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178021, d178907, d180060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40643 q ha hb
  have h3 (q : Pattern) (ha : d178022 q = 1) (hb : d178908 q = 1) : d180061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178022, d178908, d180061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178022, d178908, d180061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d178023 q = 1) (hb : d178909 q = 1) : d180062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178023, d178909, d180062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178023, d178909, d180062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177961 q = 1) (hb : d178912 q = 1) : d180063 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177961, d178912, d180063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40643 q ha hb
    | true =>
      simp only [d177961, d178912, d180063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40658 q ha hb
  have h6 (q : Pattern) (ha : d177962 q = 1) (hb : d178913 q = 1) : d180064 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177962, d178913, d180064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177962, d178913, d180064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177963 q = 1) (hb : d178914 q = 1) : d180065 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177963, d178914, d180065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177963, d178914, d180065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178024 q = 1) (hb : d178915 q = 1) : d180066 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178024, d178915, d180066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178024, d178915, d180066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177961 q = 1) (hb : d178847 q = 1) : d180000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40643 q ha hb
    | true =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
  have h10 (q : Pattern) (ha : d177962 q = 1) (hb : d178848 q = 1) : d180001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d177963 q = 1) (hb : d178849 q = 1) : d180002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d177964 q = 1) (hb : d178850 q = 1) : d180003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
    | true =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d177965 q = 1) (hb : d178851 q = 1) : d180004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d177966 q = 1) (hb : d178852 q = 1) : d180005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d177967 q = 1) (hb : d178853 q = 1) : d180006 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178025 q = 1) (hb : d178916 q = 1) : d180067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178025, d178916, d180067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178025, d178916, d180067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178026 q = 1) (hb : d178917 q = 1) : d180068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178026, d178917, d180068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d178026, d178917, d180068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h18 p ha hb
theorem andIntro40660 (p : Pattern) (ha : d178032 p = 1) (hb : d178923 p = 1) : d180074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178027 q = 1) (hb : d178918 q = 1) : d180069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178027, d178918, d180069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40659 q ha hb
    | true =>
      simp only [d178027, d178918, d180069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178028 q = 1) (hb : d178919 q = 1) : d180070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178028, d178919, d180070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178028, d178919, d180070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178029 q = 1) (hb : d178920 q = 1) : d180071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178029, d178920, d180071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178029, d178920, d180071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178030 q = 1) (hb : d178921 q = 1) : d180072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178030, d178921, d180072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178030, d178921, d180072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178031 q = 1) (hb : d178922 q = 1) : d180073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178031, d178922, d180073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178031, d178922, d180073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178032 q = 1) (hb : d178923 q = 1) : d180074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178032, d178923, d180074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178032, d178923, d180074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40661 (p : Pattern) (ha : d178040 p = 1) (hb : d178856 p = 1) : d180009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177961 q = 1) (hb : d178847 q = 1) : d180000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40643 q ha hb
    | true =>
      simp only [d177961, d178847, d180000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
  have h2 (q : Pattern) (ha : d177962 q = 1) (hb : d178848 q = 1) : d180001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177962, d178848, d180001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177963 q = 1) (hb : d178849 q = 1) : d180002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177963, d178849, d180002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d177964 q = 1) (hb : d178850 q = 1) : d180003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
    | true =>
      simp only [d177964, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d177965 q = 1) (hb : d178851 q = 1) : d180004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177965, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177966 q = 1) (hb : d178852 q = 1) : d180005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177966, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177967 q = 1) (hb : d178853 q = 1) : d180006 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177967, d178853, d180006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178035 q = 1) (hb : d178850 q = 1) : d180003 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178035, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40645 q ha hb
    | true =>
      simp only [d178035, d178850, d180003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d178036 q = 1) (hb : d178851 q = 1) : d180004 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178036, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178036, d178851, d180004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178037 q = 1) (hb : d178852 q = 1) : d180005 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178037, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178037, d178852, d180005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d178038 q = 1) (hb : d178854 q = 1) : d180007 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178038, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178038, d178854, d180007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d178039 q = 1) (hb : d178855 q = 1) : d180008 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178039, d178855, d180008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178039, d178855, d180008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178040 q = 1) (hb : d178856 q = 1) : d180009 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178040, d178856, d180009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178040, d178856, d180009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40662 (p : Pattern) (ha : d178046 p = 1) (hb : d178929 p = 1) : d180080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178041 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178041, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40661 q ha hb
    | true =>
      simp only [d178041, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178042 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178042, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178042, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178043 q = 1) (hb : d178926 q = 1) : d180077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178043, d178926, d180077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178043, d178926, d180077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178044 q = 1) (hb : d178927 q = 1) : d180078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178044, d178927, d180078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178044, d178927, d180078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178045 q = 1) (hb : d178928 q = 1) : d180079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178045, d178928, d180079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178045, d178928, d180079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178046 q = 1) (hb : d178929 q = 1) : d180080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178046, d178929, d180080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178046, d178929, d180080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40663 (p : Pattern) (ha : d178052 p = 1) (hb : d178935 p = 1) : d180086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178008 q = 1) (hb : d178894 q = 1) : d180047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178008, d178894, d180047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40654 q ha hb
    | true =>
      simp only [d178008, d178894, d180047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40655 q ha hb
  have h2 (q : Pattern) (ha : d178009 q = 1) (hb : d178895 q = 1) : d180048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178009, d178895, d180048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178009, d178895, d180048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178010 q = 1) (hb : d178896 q = 1) : d180049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178010, d178896, d180049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178010, d178896, d180049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178011 q = 1) (hb : d178897 q = 1) : d180050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178011, d178897, d180050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178011, d178897, d180050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178018 q = 1) (hb : d178904 q = 1) : d180057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178018, d178904, d180057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40656 q ha hb
    | true =>
      simp only [d178018, d178904, d180057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40657 q ha hb
  have h6 (q : Pattern) (ha : d178019 q = 1) (hb : d178905 q = 1) : d180058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178019, d178905, d180058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178019, d178905, d180058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178020 q = 1) (hb : d178906 q = 1) : d180059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178020, d178906, d180059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178020, d178906, d180059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178033 q = 1) (hb : d178924 q = 1) : d180075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178033, d178924, d180075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40660 q ha hb
    | true =>
      simp only [d178033, d178924, d180075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177985 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d178034 q = 1) (hb : d178925 q = 1) : d180076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178034, d178925, d180076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178034, d178925, d180076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d178047 q = 1) (hb : d178930 q = 1) : d180081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178047, d178930, d180081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40662 q ha hb
    | true =>
      simp only [d178047, d178930, d180081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d178048 q = 1) (hb : d178931 q = 1) : d180082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178048, d178931, d180082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178048, d178931, d180082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d178049 q = 1) (hb : d178932 q = 1) : d180083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178049, d178932, d180083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178049, d178932, d180083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178050 q = 1) (hb : d178933 q = 1) : d180084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178050, d178933, d180084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178050, d178933, d180084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d178051 q = 1) (hb : d178934 q = 1) : d180085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178051, d178934, d180085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178051, d178934, d180085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178052 q = 1) (hb : d178935 q = 1) : d180086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178052, d178935, d180086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178052, d178935, d180086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro40664 (p : Pattern) (ha : d178053 p = 1) (hb : d178936 p = 1) : d180087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177978 q = 1) (hb : d178864 q = 1) : d180017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177978, d178864, d180017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178004 q = 1) (hb : d178890 q = 1) : d180043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178004, d178890, d180043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178004, d178890, d180043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178053 q = 1) (hb : d178936 q = 1) : d180087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178053, d178936, d180087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178053, d178936, d180087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40665 (p : Pattern) (ha : d178054 p = 1) (hb : d178937 p = 1) : d180088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177982 q = 1) (hb : d178868 q = 1) : d180021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177982, d178868, d180021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178006 q = 1) (hb : d178892 q = 1) : d180045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178006, d178892, d180045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178006, d178892, d180045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178054 q = 1) (hb : d178937 q = 1) : d180088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178054, d178937, d180088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178054, d178937, d180088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40666 (p : Pattern) (ha : d178059 p = 1) (hb : d178942 p = 1) : d180093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177977 q = 1) (hb : d178863 q = 1) : d180016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177977, d178863, d180016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178012 q = 1) (hb : d178898 q = 1) : d180051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178012, d178898, d180051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178012, d178898, d180051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178013 q = 1) (hb : d178899 q = 1) : d180052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178013, d178899, d180052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178013, d178899, d180052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178059 q = 1) (hb : d178942 q = 1) : d180093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178059, d178942, d180093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178059, d178942, d180093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40667 (p : Pattern) (ha : d178060 p = 1) (hb : d178943 p = 1) : d180094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177975 q = 1) (hb : d178861 q = 1) : d180014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40647 q ha hb
    | true =>
      simp only [d177975, d178861, d180014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d177976 q = 1) (hb : d178862 q = 1) : d180015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177976, d178862, d180015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177981 q = 1) (hb : d178867 q = 1) : d180020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177981, d178867, d180020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178015 q = 1) (hb : d178901 q = 1) : d180054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178015, d178901, d180054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178015, d178901, d180054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178016 q = 1) (hb : d178902 q = 1) : d180055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178016, d178902, d180055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178016, d178902, d180055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178060 q = 1) (hb : d178943 q = 1) : d180094 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178060, d178943, d180094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178060, d178943, d180094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40668 (p : Pattern) (ha : d178064 p = 1) (hb : d178947 p = 1) : d180098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178027 q = 1) (hb : d178918 q = 1) : d180069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178027, d178918, d180069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40659 q ha hb
    | true =>
      simp only [d178027, d178918, d180069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178028 q = 1) (hb : d178919 q = 1) : d180070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178028, d178919, d180070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178028, d178919, d180070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177971 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40646 q ha hb
    | true =>
      simp only [d177971, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177972 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177972, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178029 q = 1) (hb : d178920 q = 1) : d180071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178029, d178920, d180071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178029, d178920, d180071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178030 q = 1) (hb : d178921 q = 1) : d180072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178030, d178921, d180072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178030, d178921, d180072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178031 q = 1) (hb : d178922 q = 1) : d180073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178031, d178922, d180073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178031, d178922, d180073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178064 q = 1) (hb : d178947 q = 1) : d180098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178064, d178947, d180098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178064, d178947, d180098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40669 (p : Pattern) (ha : d178067 p = 1) (hb : d178950 p = 1) : d180101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178041 q = 1) (hb : d178857 q = 1) : d180010 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178041, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40661 q ha hb
    | true =>
      simp only [d178041, d178857, d180010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178042 q = 1) (hb : d178858 q = 1) : d180011 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178042, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178042, d178858, d180011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178043 q = 1) (hb : d178926 q = 1) : d180077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178043, d178926, d180077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178043, d178926, d180077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178044 q = 1) (hb : d178927 q = 1) : d180078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178044, d178927, d180078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178044, d178927, d180078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178045 q = 1) (hb : d178928 q = 1) : d180079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178045, d178928, d180079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178045, d178928, d180079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178067 q = 1) (hb : d178950 q = 1) : d180101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178067, d178950, d180101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178067, d178950, d180101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40670 (p : Pattern) (ha : d178073 p = 1) (hb : d178956 p = 1) : d180107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178008 q = 1) (hb : d178894 q = 1) : d180047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178008, d178894, d180047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40654 q ha hb
    | true =>
      simp only [d178008, d178894, d180047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40655 q ha hb
  have h2 (q : Pattern) (ha : d178009 q = 1) (hb : d178895 q = 1) : d180048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178009, d178895, d180048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178009, d178895, d180048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178010 q = 1) (hb : d178896 q = 1) : d180049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178010, d178896, d180049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178010, d178896, d180049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178011 q = 1) (hb : d178897 q = 1) : d180050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178011, d178897, d180050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178011, d178897, d180050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178018 q = 1) (hb : d178904 q = 1) : d180057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178018, d178904, d180057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40656 q ha hb
    | true =>
      simp only [d178018, d178904, d180057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40657 q ha hb
  have h6 (q : Pattern) (ha : d178019 q = 1) (hb : d178905 q = 1) : d180058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178019, d178905, d180058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178019, d178905, d180058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178020 q = 1) (hb : d178906 q = 1) : d180059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178020, d178906, d180059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178020, d178906, d180059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178033 q = 1) (hb : d178924 q = 1) : d180075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178033, d178924, d180075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40660 q ha hb
    | true =>
      simp only [d178033, d178924, d180075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177985 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d178034 q = 1) (hb : d178925 q = 1) : d180076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178034, d178925, d180076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178034, d178925, d180076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d178047 q = 1) (hb : d178930 q = 1) : d180081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178047, d178930, d180081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40662 q ha hb
    | true =>
      simp only [d178047, d178930, d180081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d178048 q = 1) (hb : d178931 q = 1) : d180082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178048, d178931, d180082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178048, d178931, d180082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d178049 q = 1) (hb : d178932 q = 1) : d180083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178049, d178932, d180083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178049, d178932, d180083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178050 q = 1) (hb : d178933 q = 1) : d180084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178050, d178933, d180084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178050, d178933, d180084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d178051 q = 1) (hb : d178934 q = 1) : d180085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178051, d178934, d180085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178051, d178934, d180085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178055 q = 1) (hb : d178938 q = 1) : d180089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178055, d178938, d180089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40664 q ha hb
    | true =>
      simp only [d178055, d178938, d180089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40665 q ha hb
  have h17 (q : Pattern) (ha : d178056 q = 1) (hb : d178939 q = 1) : d180090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178056, d178939, d180090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178056, d178939, d180090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178057 q = 1) (hb : d178940 q = 1) : d180091 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178057, d178940, d180091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d178057, d178940, d180091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d178058 q = 1) (hb : d178941 q = 1) : d180092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178058, d178941, d180092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178058, d178941, d180092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d178061 q = 1) (hb : d178944 q = 1) : d180095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178061, d178944, d180095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40666 q ha hb
    | true =>
      simp only [d178061, d178944, d180095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40667 q ha hb
  have h21 (q : Pattern) (ha : d178062 q = 1) (hb : d178945 q = 1) : d180096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178062, d178945, d180096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178062, d178945, d180096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d178063 q = 1) (hb : d178946 q = 1) : d180097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178063, d178946, d180097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d178063, d178946, d180097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d178065 q = 1) (hb : d178948 q = 1) : d180099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178065, d178948, d180099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40668 q ha hb
    | true =>
      simp only [d178065, d178948, d180099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40651 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d177995 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d178066 q = 1) (hb : d178949 q = 1) : d180100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178066, d178949, d180100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d178066, d178949, d180100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d178068 q = 1) (hb : d178951 q = 1) : d180102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178068, d178951, d180102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40669 q ha hb
    | true =>
      simp only [d178068, d178951, d180102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d178069 q = 1) (hb : d178952 q = 1) : d180103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178069, d178952, d180103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d178069, d178952, d180103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d178070 q = 1) (hb : d178953 q = 1) : d180104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178070, d178953, d180104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d178070, d178953, d180104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d178071 q = 1) (hb : d178954 q = 1) : d180105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178071, d178954, d180105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d178071, d178954, d180105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d178072 q = 1) (hb : d178955 q = 1) : d180106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178072, d178955, d180106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d178072, d178955, d180106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d178073 q = 1) (hb : d178956 q = 1) : d180107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178073, d178956, d180107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d178073, d178956, d180107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro40671 (p : Pattern) (ha : d178080 p = 1) (hb : d178963 p = 1) : d180114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177985 q = 1) (hb : d178871 q = 1) : d180024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40648 q ha hb
    | true =>
      simp only [d177985, d178871, d180024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
  have h2 (q : Pattern) (ha : d177986 q = 1) (hb : d178872 q = 1) : d180025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177986, d178872, d180025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d177987 q = 1) (hb : d178873 q = 1) : d180026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d177987, d178873, d180026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d177988 q = 1) (hb : d178874 q = 1) : d180027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177988, d178874, d180027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d177989 q = 1) (hb : d178875 q = 1) : d180028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177989, d178875, d180028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178075 q = 1) (hb : d178958 q = 1) : d180109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178075, d178958, d180109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
    | true =>
      simp only [d178075, d178958, d180109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178076 q = 1) (hb : d178959 q = 1) : d180110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178076, d178959, d180110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178076, d178959, d180110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178077 q = 1) (hb : d178960 q = 1) : d180111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178077, d178960, d180111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178077, d178960, d180111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d178078 q = 1) (hb : d178961 q = 1) : d180112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178078, d178961, d180112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178078, d178961, d180112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178079 q = 1) (hb : d178962 q = 1) : d180113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178079, d178962, d180113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178079, d178962, d180113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178080 q = 1) (hb : d178963 q = 1) : d180114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178080, d178963, d180114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178080, d178963, d180114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40672 (p : Pattern) (ha : d178086 p = 1) (hb : d178969 p = 1) : d180120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178075 q = 1) (hb : d178958 q = 1) : d180109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178075, d178958, d180109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40649 q ha hb
    | true =>
      simp only [d178075, d178958, d180109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178076 q = 1) (hb : d178959 q = 1) : d180110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178076, d178959, d180110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178076, d178959, d180110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178077 q = 1) (hb : d178960 q = 1) : d180111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178077, d178960, d180111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178077, d178960, d180111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178078 q = 1) (hb : d178961 q = 1) : d180112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178078, d178961, d180112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178078, d178961, d180112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178079 q = 1) (hb : d178962 q = 1) : d180113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178079, d178962, d180113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178079, d178962, d180113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178081 q = 1) (hb : d178964 q = 1) : d180115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178081, d178964, d180115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40652 q ha hb
    | true =>
      simp only [d178081, d178964, d180115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178082 q = 1) (hb : d178965 q = 1) : d180116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178082, d178965, d180116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178082, d178965, d180116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178083 q = 1) (hb : d178966 q = 1) : d180117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178083, d178966, d180117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178083, d178966, d180117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d178084 q = 1) (hb : d178967 q = 1) : d180118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178084, d178967, d180118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178084, d178967, d180118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d178085 q = 1) (hb : d178968 q = 1) : d180119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178085, d178968, d180119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178085, d178968, d180119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178086 q = 1) (hb : d178969 q = 1) : d180120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178086, d178969, d180120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178086, d178969, d180120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40673 (p : Pattern) (ha : d178093 p = 1) (hb : d178976 p = 1) : d180127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178065 q = 1) (hb : d178948 q = 1) : d180099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178065, d178948, d180099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40668 q ha hb
    | true =>
      simp only [d178065, d178948, d180099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40651 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178066 q = 1) (hb : d178949 q = 1) : d180100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178066, d178949, d180100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178066, d178949, d180100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d178068 q = 1) (hb : d178951 q = 1) : d180102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178068, d178951, d180102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40669 q ha hb
    | true =>
      simp only [d178068, d178951, d180102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178069 q = 1) (hb : d178952 q = 1) : d180103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178069, d178952, d180103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178069, d178952, d180103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178070 q = 1) (hb : d178953 q = 1) : d180104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178070, d178953, d180104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178070, d178953, d180104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178091 q = 1) (hb : d178974 q = 1) : d180125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178091, d178974, d180125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178091, d178974, d180125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178092 q = 1) (hb : d178975 q = 1) : d180126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178092, d178975, d180126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178092, d178975, d180126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178093 q = 1) (hb : d178976 q = 1) : d180127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178093, d178976, d180127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178093, d178976, d180127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40674 (p : Pattern) (ha : d178095 p = 1) (hb : d178978 p = 1) : d180129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178081 q = 1) (hb : d178964 q = 1) : d180115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178081, d178964, d180115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40652 q ha hb
    | true =>
      simp only [d178081, d178964, d180115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178082 q = 1) (hb : d178965 q = 1) : d180116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178082, d178965, d180116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178082, d178965, d180116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178083 q = 1) (hb : d178966 q = 1) : d180117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178083, d178966, d180117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178083, d178966, d180117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178084 q = 1) (hb : d178967 q = 1) : d180118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178084, d178967, d180118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178084, d178967, d180118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178085 q = 1) (hb : d178968 q = 1) : d180119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178085, d178968, d180119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178085, d178968, d180119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178095 q = 1) (hb : d178978 q = 1) : d180129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178095, d178978, d180129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178095, d178978, d180129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40675 (p : Pattern) (ha : d113968 p = 1) (hb : d178985 p = 1) : d180140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17376 q = 1) (hb : d113965 q = 1) : d180135 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d113965, d180135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17376, d113965, d180135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40642 q ha hb
  have h3 (q : Pattern) (ha : d10364 q = 1) (hb : d101674 q = 1) : d179984 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101674, d179984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40642 q ha hb
    | true =>
      simp only [d10364, d101674, d179984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17377 q = 1) (hb : d113966 q = 1) : d180136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d113966, d180136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17377, d113966, d180136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10366 q = 1) (hb : d101676 q = 1) : d179985 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101676, d179985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10366, d101676, d179985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17378 q = 1) (hb : d113967 q = 1) : d180137 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d113967, d180137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17378, d113967, d180137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17379 q = 1) (hb : d113968 q = 1) : d180138 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d113968, d180138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17379, d113968, d180138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d113968 q = 1) (hb : d178984 q = 1) : d180139 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178984, d180139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178984, d180139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d113968 q = 1) (hb : d178985 q = 1) : d180140 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178985, d180140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178985, d180140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40676 (p : Pattern) (ha : d123731 p = 1) (hb : d178990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123731 q = 1) (hb : d178989 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123731 q = 1) (hb : d178990 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40677 (p : Pattern) (ha : d123731 p = 1) (hb : d178996 p = 1) : d180153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17391 q = 1) (hb : d123728 q = 1) : d180148 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d123728, d180148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17391, d123728, d180148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40644 q ha hb
  have h3 (q : Pattern) (ha : d10391 q = 1) (hb : d101692 q = 1) : d179994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101692, d179994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40644 q ha hb
    | true =>
      simp only [d10391, d101692, d179994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17392 q = 1) (hb : d123729 q = 1) : d180149 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d123729, d180149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17392, d123729, d180149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10393 q = 1) (hb : d101694 q = 1) : d179995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101694, d179995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10393, d101694, d179995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17393 q = 1) (hb : d123730 q = 1) : d180150 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d123730, d180150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17393, d123730, d180150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17394 q = 1) (hb : d123731 q = 1) : d180151 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d123731, d180151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17394, d123731, d180151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123731 q = 1) (hb : d178995 q = 1) : d180152 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d178995, d180152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178995, d180152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d123731 q = 1) (hb : d178996 q = 1) : d180153 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d178996, d180153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178996, d180153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro40678 (p : Pattern) (ha : d178113 p = 1) (hb : d179005 p = 1) : d180162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d149666 q = 1) : d149666 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d178101 q = 1) (hb : d178986 q = 1) : d180141 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178101, d178986, d180141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178101, d178986, d180141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40675 q ha hb
  have h3 (q : Pattern) (ha : d178102 q = 1) (hb : d178987 q = 1) : d180142 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178102, d178987, d180142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178102, d178987, d180142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d178103 q = 1) (hb : d178988 q = 1) : d180143 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178103, d178988, d180143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178103, d178988, d180143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178104 q = 1) (hb : d178991 q = 1) : d180144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178104, d178991, d180144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40675 q ha hb
    | true =>
      simp only [d178104, d178991, d180144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40676 q ha hb
  have h6 (q : Pattern) (ha : d178105 q = 1) (hb : d178992 q = 1) : d180145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178105, d178992, d180145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178105, d178992, d180145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178106 q = 1) (hb : d178993 q = 1) : d180146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178106, d178993, d180146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178106, d178993, d180146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178107 q = 1) (hb : d178994 q = 1) : d180147 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178107, d178994, d180147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178107, d178994, d180147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178104 q = 1) (hb : d178997 q = 1) : d180154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40675 q ha hb
    | true =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
  have h10 (q : Pattern) (ha : d178105 q = 1) (hb : d178998 q = 1) : d180155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178106 q = 1) (hb : d178999 q = 1) : d180156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d178108 q = 1) (hb : d179000 q = 1) : d180157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
    | true =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d178109 q = 1) (hb : d179001 q = 1) : d180158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d178110 q = 1) (hb : d179002 q = 1) : d180159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178111 q = 1) (hb : d179003 q = 1) : d180160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178112 q = 1) (hb : d179004 q = 1) : d180161 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178112, d179004, d180161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178112, d179004, d180161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d178113 q = 1) (hb : d179005 q = 1) : d180162 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178113, d179005, d180162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d178113, d179005, d180162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h18 p ha hb
theorem andIntro40679 (p : Pattern) (ha : d178118 p = 1) (hb : d179010 p = 1) : d180167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178104 q = 1) (hb : d178997 q = 1) : d180154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40675 q ha hb
    | true =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
  have h2 (q : Pattern) (ha : d178105 q = 1) (hb : d178998 q = 1) : d180155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178106 q = 1) (hb : d178999 q = 1) : d180156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178108 q = 1) (hb : d179000 q = 1) : d180157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
    | true =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d178109 q = 1) (hb : d179001 q = 1) : d180158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178110 q = 1) (hb : d179002 q = 1) : d180159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178111 q = 1) (hb : d179003 q = 1) : d180160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178116 q = 1) (hb : d179008 q = 1) : d180165 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178116, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178116, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d178117 q = 1) (hb : d179009 q = 1) : d180166 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178117, d179009, d180166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178117, d179009, d180166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178118 q = 1) (hb : d179010 q = 1) : d180167 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178118, d179010, d180167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178118, d179010, d180167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro40680 (p : Pattern) (ha : d178124 p = 1) (hb : d179016 p = 1) : d180173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178114 q = 1) (hb : d179006 q = 1) : d180163 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178114, d179006, d180163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40678 q ha hb
    | true =>
      simp only [d178114, d179006, d180163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178115 q = 1) (hb : d179007 q = 1) : d180164 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178115, d179007, d180164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178115, d179007, d180164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178119 q = 1) (hb : d179011 q = 1) : d180168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178119, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40679 q ha hb
    | true =>
      simp only [d178119, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178120 q = 1) (hb : d179012 q = 1) : d180169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178120, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178120, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178121 q = 1) (hb : d179013 q = 1) : d180170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178121, d179013, d180170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178121, d179013, d180170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178122 q = 1) (hb : d179014 q = 1) : d180171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178122, d179014, d180171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178122, d179014, d180171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178123 q = 1) (hb : d179015 q = 1) : d180172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178123, d179015, d180172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178123, d179015, d180172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178124 q = 1) (hb : d179016 q = 1) : d180173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178124, d179016, d180173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178124, d179016, d180173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40681 (p : Pattern) (ha : d178126 p = 1) (hb : d179018 p = 1) : d180175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d178108 q = 1) (hb : d179000 q = 1) : d180157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
    | true =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d178109 q = 1) (hb : d179001 q = 1) : d180158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d178110 q = 1) (hb : d179002 q = 1) : d180159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178116 q = 1) (hb : d179008 q = 1) : d180165 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178116, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178116, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178125 q = 1) (hb : d179017 q = 1) : d180174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178125, d179017, d180174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178125, d179017, d180174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178126 q = 1) (hb : d179018 q = 1) : d180175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178126, d179018, d180175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178126, d179018, d180175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro40682 (p : Pattern) (ha : d178132 p = 1) (hb : d179024 p = 1) : d180181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178119 q = 1) (hb : d179011 q = 1) : d180168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178119, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40679 q ha hb
    | true =>
      simp only [d178119, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178120 q = 1) (hb : d179012 q = 1) : d180169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178120, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178120, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178127 q = 1) (hb : d179019 q = 1) : d180176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178127, d179019, d180176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40681 q ha hb
    | true =>
      simp only [d178127, d179019, d180176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178128 q = 1) (hb : d179020 q = 1) : d180177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178128, d179020, d180177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178128, d179020, d180177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178129 q = 1) (hb : d179021 q = 1) : d180178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178129, d179021, d180178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178129, d179021, d180178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178130 q = 1) (hb : d179022 q = 1) : d180179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178130, d179022, d180179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178130, d179022, d180179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d178131 q = 1) (hb : d179023 q = 1) : d180180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178131, d179023, d180180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178131, d179023, d180180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d178132 q = 1) (hb : d179024 q = 1) : d180181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178132, d179024, d180181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d178132, d179024, d180181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40683 (p : Pattern) (ha : d178145 p = 1) (hb : d179010 p = 1) : d180167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178104 q = 1) (hb : d178997 q = 1) : d180154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40675 q ha hb
    | true =>
      simp only [d178104, d178997, d180154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
  have h2 (q : Pattern) (ha : d178105 q = 1) (hb : d178998 q = 1) : d180155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178105, d178998, d180155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178106 q = 1) (hb : d178999 q = 1) : d180156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178106, d178999, d180156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d178108 q = 1) (hb : d179000 q = 1) : d180157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
    | true =>
      simp only [d178108, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d178109 q = 1) (hb : d179001 q = 1) : d180158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178109, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178110 q = 1) (hb : d179002 q = 1) : d180159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178110, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178111 q = 1) (hb : d179003 q = 1) : d180160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178111, d179003, d180160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178140 q = 1) (hb : d179000 q = 1) : d180157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d178140, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40677 q ha hb
    | true =>
      simp only [d178140, d179000, d180157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d178141 q = 1) (hb : d179001 q = 1) : d180158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d178141, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178141, d179001, d180158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178142 q = 1) (hb : d179002 q = 1) : d180159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178142, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178142, d179002, d180159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d178143 q = 1) (hb : d179008 q = 1) : d180165 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d178143, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178143, d179008, d180165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d178144 q = 1) (hb : d179009 q = 1) : d180166 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d178144, d179009, d180166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178144, d179009, d180166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178145 q = 1) (hb : d179010 q = 1) : d180167 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d178145, d179010, d180167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178145, d179010, d180167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro40684 (p : Pattern) (ha : d178151 p = 1) (hb : d179030 p = 1) : d180187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178146 q = 1) (hb : d179011 q = 1) : d180168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178146, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40683 q ha hb
    | true =>
      simp only [d178146, d179011, d180168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178147 q = 1) (hb : d179012 q = 1) : d180169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178147, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178147, d179012, d180169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178148 q = 1) (hb : d179027 q = 1) : d180184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178148, d179027, d180184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178148, d179027, d180184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178149 q = 1) (hb : d179028 q = 1) : d180185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178149, d179028, d180185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178149, d179028, d180185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178150 q = 1) (hb : d179029 q = 1) : d180186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178150, d179029, d180186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178150, d179029, d180186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178151 q = 1) (hb : d179030 q = 1) : d180187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178151, d179030, d180187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178151, d179030, d180187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40685 (p : Pattern) (ha : d178157 p = 1) (hb : d179036 p = 1) : d180193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178133 q = 1) (hb : d179025 q = 1) : d180182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178133, d179025, d180182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40680 q ha hb
    | true =>
      simp only [d178133, d179025, d180182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40682 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d178138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d178139 q = 1) (hb : d179026 q = 1) : d180183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178139, d179026, d180183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178139, d179026, d180183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d178152 q = 1) (hb : d179031 q = 1) : d180188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178152, d179031, d180188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40684 q ha hb
    | true =>
      simp only [d178152, d179031, d180188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178153 q = 1) (hb : d179032 q = 1) : d180189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178153, d179032, d180189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178153, d179032, d180189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178154 q = 1) (hb : d179033 q = 1) : d180190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178154, d179033, d180190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178154, d179033, d180190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d178155 q = 1) (hb : d179034 q = 1) : d180191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178155, d179034, d180191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178155, d179034, d180191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d178156 q = 1) (hb : d179035 q = 1) : d180192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178156, d179035, d180192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178156, d179035, d180192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178157 q = 1) (hb : d179036 q = 1) : d180193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178157, d179036, d180193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178157, d179036, d180193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro40686 (p : Pattern) (ha : d178137 p = 1) (hb : d179041 p = 1) : d180198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178127 q = 1) (hb : d179019 q = 1) : d180176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d178127, d179019, d180176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40681 q ha hb
    | true =>
      simp only [d178127, d179019, d180176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178128 q = 1) (hb : d179020 q = 1) : d180177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d178128, d179020, d180177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178128, d179020, d180177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178134 q = 1) (hb : d179038 q = 1) : d180195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d178134, d179038, d180195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178134, d179038, d180195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178135 q = 1) (hb : d179039 q = 1) : d180196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d178135, d179039, d180196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178135, d179039, d180196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178136 q = 1) (hb : d179040 q = 1) : d180197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d178136, d179040, d180197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178136, d179040, d180197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178137 q = 1) (hb : d179041 q = 1) : d180198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d178137, d179041, d180198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178137, d179041, d180198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40687 (p : Pattern) (ha : d178164 p = 1) (hb : d179047 p = 1) : d180204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178159 q = 1) (hb : d179042 q = 1) : d180199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d178159, d179042, d180199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40686 q ha hb
    | true =>
      simp only [d178159, d179042, d180199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178160 q = 1) (hb : d179043 q = 1) : d180200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d178160, d179043, d180200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178160, d179043, d180200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178161 q = 1) (hb : d179044 q = 1) : d180201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d178161, d179044, d180201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178161, d179044, d180201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178162 q = 1) (hb : d179045 q = 1) : d180202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d178162, d179045, d180202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178162, d179045, d180202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178163 q = 1) (hb : d179046 q = 1) : d180203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d178163, d179046, d180203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178163, d179046, d180203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178164 q = 1) (hb : d179047 q = 1) : d180204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d178164, d179047, d180204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178164, d179047, d180204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40688 (p : Pattern) (ha : d178170 p = 1) (hb : d179053 p = 1) : d180210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d177991 q = 1) (hb : d178877 q = 1) : d180030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177991, d178877, d180030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177991, d178877, d180030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40650 q ha hb
  have h2 (q : Pattern) (ha : d177992 q = 1) (hb : d178878 q = 1) : d180031 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177992, d178878, d180031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d177992, d178878, d180031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178001 q = 1) (hb : d178887 q = 1) : d180040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178001, d178887, d180040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40650 q ha hb
    | true =>
      simp only [d178001, d178887, d180040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40653 q ha hb
  have h4 (q : Pattern) (ha : d178002 q = 1) (hb : d178888 q = 1) : d180041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178002, d178888, d180041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178002, d178888, d180041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178003 q = 1) (hb : d178889 q = 1) : d180042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178003, d178889, d180042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178003, d178889, d180042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178074 q = 1) (hb : d178957 q = 1) : d180108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178074, d178957, d180108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40663 q ha hb
    | true =>
      simp only [d178074, d178957, d180108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40670 q ha hb
  have h7 (q : Pattern) (ha : d178087 q = 1) (hb : d178970 q = 1) : d180121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178087, d178970, d180121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40671 q ha hb
    | true =>
      simp only [d178087, d178970, d180121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40672 q ha hb
  have h8 (q : Pattern) (ha : d178088 q = 1) (hb : d178971 q = 1) : d180122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178088, d178971, d180122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d178088, d178971, d180122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d178089 q = 1) (hb : d178972 q = 1) : d180123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178089, d178972, d180123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d178089, d178972, d180123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d178090 q = 1) (hb : d178973 q = 1) : d180124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178090, d178973, d180124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178090, d178973, d180124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178094 q = 1) (hb : d178977 q = 1) : d180128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178094, d178977, d180128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178094, d178977, d180128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40673 q ha hb
  have h12 (q : Pattern) (ha : d178096 q = 1) (hb : d178979 q = 1) : d180130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178096, d178979, d180130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178096, d178979, d180130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40674 q ha hb
  have h13 (q : Pattern) (ha : d178097 q = 1) (hb : d178980 q = 1) : d180131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178097, d178980, d180131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d178097, d178980, d180131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178098 q = 1) (hb : d178981 q = 1) : d180132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178098, d178981, d180132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d178098, d178981, d180132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d178099 q = 1) (hb : d178982 q = 1) : d180133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178099, d178982, d180133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d178099, d178982, d180133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d178100 q = 1) (hb : d178983 q = 1) : d180134 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d178100, d178983, d180134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178100, d178983, d180134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d178158 q = 1) (hb : d179037 q = 1) : d180194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178158, d179037, d180194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178158, d179037, d180194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40685 q ha hb
  have h18 (q : Pattern) (ha : d178165 q = 1) (hb : d179048 q = 1) : d180205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d178165, d179048, d180205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178165, d179048, d180205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40687 q ha hb
  have h19 (q : Pattern) (ha : d178166 q = 1) (hb : d179049 q = 1) : d180206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d178166, d179049, d180206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d178166, d179049, d180206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d178167 q = 1) (hb : d179050 q = 1) : d180207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d178167, d179050, d180207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d178167, d179050, d180207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d178168 q = 1) (hb : d179051 q = 1) : d180208 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d178168, d179051, d180208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d178168, d179051, d180208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d178169 q = 1) (hb : d179052 q = 1) : d180209 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d178169, d179052, d180209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d178169, d179052, d180209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d178170 q = 1) (hb : d179053 q = 1) : d180210 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d178170, d179053, d180210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d178170, d179053, d180210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40689 (p : Pattern) (ha : d178176 p = 1) (hb : d179059 p = 1) : d180216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178171 q = 1) (hb : d179054 q = 1) : d180211 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d178171, d179054, d180211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178171, d179054, d180211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40688 q ha hb
  have h2 (q : Pattern) (ha : d178172 q = 1) (hb : d179055 q = 1) : d180212 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d178172, d179055, d180212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178172, d179055, d180212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d178173 q = 1) (hb : d179056 q = 1) : d180213 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d178173, d179056, d180213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178173, d179056, d180213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d178174 q = 1) (hb : d179057 q = 1) : d180214 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d178174, d179057, d180214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178174, d179057, d180214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d178175 q = 1) (hb : d179058 q = 1) : d180215 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d178175, d179058, d180215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178175, d179058, d180215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d178176 q = 1) (hb : d179059 q = 1) : d180216 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d178176, d179059, d180216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d178176, d179059, d180216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40690 (p : Pattern) (ha : d178182 p = 1) (hb : d179065 p = 1) : d180222 p = 1 := by
  have h0 (q : Pattern) (ha : d177371 q = 1) (hb : d178296 q = 1) : d179299 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177371, d178296, d179299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40467 q hb ha
    | true =>
      simp only [d177371, d178296, d179299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40494 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d177520 q = 1) (hb : d178448 q = 1) : d179458 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177520, d178448, d179458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177520, d178448, d179458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40538 q ha hb
  have h3 (q : Pattern) (ha : d177521 q = 1) (hb : d178449 q = 1) : d179459 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177521, d178449, d179459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d177521, d178449, d179459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d177738 q = 1) (hb : d178615 q = 1) : d179717 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177738, d178615, d179717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177738, d178615, d179717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40589 q ha hb
  have h5 (q : Pattern) (ha : d177739 q = 1) (hb : d178616 q = 1) : d179718 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177739, d178616, d179718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177739, d178616, d179718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d177740 q = 1) (hb : d178617 q = 1) : d179719 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177740, d178617, d179719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d177740, d178617, d179719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d177957 q = 1) (hb : d178839 q = 1) : d179976 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177957, d178839, d179976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177957, d178839, d179976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40641 q ha hb
  have h8 (q : Pattern) (ha : d177958 q = 1) (hb : d178840 q = 1) : d179977 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177958, d178840, d179977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177958, d178840, d179977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177959 q = 1) (hb : d178841 q = 1) : d179978 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177959, d178841, d179978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177959, d178841, d179978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177960 q = 1) (hb : d178842 q = 1) : d179979 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d177960, d178842, d179979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d177960, d178842, d179979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d178177 q = 1) (hb : d179060 q = 1) : d180217 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d178177, d179060, d180217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178177, d179060, d180217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40689 q ha hb
  have h12 (q : Pattern) (ha : d178178 q = 1) (hb : d179061 q = 1) : d180218 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d178178, d179061, d180218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178178, d179061, d180218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d178179 q = 1) (hb : d179062 q = 1) : d180219 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d178179, d179062, d180219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178179, d179062, d180219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d178180 q = 1) (hb : d179063 q = 1) : d180220 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d178180, d179063, d180220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d178180, d179063, d180220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d178181 q = 1) (hb : d179064 q = 1) : d180221 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d178181, d179064, d180221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d178181, d179064, d180221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d178182 q = 1) (hb : d179065 q = 1) : d180222 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d178182, d179065, d180222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d178182, d179065, d180222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro40691 (p : Pattern) (ha : d178188 p = 1) (hb : d179071 p = 1) : d180228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178183 q = 1) (hb : d179066 q = 1) : d180223 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d178183, d179066, d180223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40690 q ha hb
    | true =>
      simp only [d178183, d179066, d180223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178184 q = 1) (hb : d179067 q = 1) : d180224 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d178184, d179067, d180224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178184, d179067, d180224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178185 q = 1) (hb : d179068 q = 1) : d180225 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d178185, d179068, d180225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178185, d179068, d180225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178186 q = 1) (hb : d179069 q = 1) : d180226 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d178186, d179069, d180226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178186, d179069, d180226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178187 q = 1) (hb : d179070 q = 1) : d180227 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d178187, d179070, d180227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178187, d179070, d180227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178188 q = 1) (hb : d179071 q = 1) : d180228 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d178188, d179071, d180228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178188, d179071, d180228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40692 (p : Pattern) (ha : d178194 p = 1) (hb : d179077 p = 1) : d180234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178189 q = 1) (hb : d179072 q = 1) : d180229 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d178189, d179072, d180229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40691 q ha hb
    | true =>
      simp only [d178189, d179072, d180229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178190 q = 1) (hb : d179073 q = 1) : d180230 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d178190, d179073, d180230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178190, d179073, d180230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178191 q = 1) (hb : d179074 q = 1) : d180231 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d178191, d179074, d180231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178191, d179074, d180231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178192 q = 1) (hb : d179075 q = 1) : d180232 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d178192, d179075, d180232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178192, d179075, d180232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178193 q = 1) (hb : d179076 q = 1) : d180233 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d178193, d179076, d180233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178193, d179076, d180233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178194 q = 1) (hb : d179077 q = 1) : d180234 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d178194, d179077, d180234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178194, d179077, d180234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40693 (p : Pattern) (ha : d178200 p = 1) (hb : d179083 p = 1) : d180240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178195 q = 1) (hb : d179078 q = 1) : d180235 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d178195, d179078, d180235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40692 q ha hb
    | true =>
      simp only [d178195, d179078, d180235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178196 q = 1) (hb : d179079 q = 1) : d180236 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d178196, d179079, d180236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178196, d179079, d180236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178197 q = 1) (hb : d179080 q = 1) : d180237 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d178197, d179080, d180237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178197, d179080, d180237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178198 q = 1) (hb : d179081 q = 1) : d180238 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d178198, d179081, d180238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178198, d179081, d180238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178199 q = 1) (hb : d179082 q = 1) : d180239 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d178199, d179082, d180239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178199, d179082, d180239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178200 q = 1) (hb : d179083 q = 1) : d180240 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d178200, d179083, d180240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178200, d179083, d180240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40694 (p : Pattern) (ha : d178206 p = 1) (hb : d179089 p = 1) : d180246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178201 q = 1) (hb : d179084 q = 1) : d180241 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d178201, d179084, d180241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40693 q ha hb
    | true =>
      simp only [d178201, d179084, d180241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178202 q = 1) (hb : d179085 q = 1) : d180242 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d178202, d179085, d180242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178202, d179085, d180242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178203 q = 1) (hb : d179086 q = 1) : d180243 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d178203, d179086, d180243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178203, d179086, d180243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178204 q = 1) (hb : d179087 q = 1) : d180244 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d178204, d179087, d180244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178204, d179087, d180244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178205 q = 1) (hb : d179088 q = 1) : d180245 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d178205, d179088, d180245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178205, d179088, d180245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178206 q = 1) (hb : d179089 q = 1) : d180246 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d178206, d179089, d180246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178206, d179089, d180246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40695 (p : Pattern) (ha : d178212 p = 1) (hb : d179095 p = 1) : d180252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178207 q = 1) (hb : d179090 q = 1) : d180247 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d178207, d179090, d180247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40694 q ha hb
    | true =>
      simp only [d178207, d179090, d180247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178208 q = 1) (hb : d179091 q = 1) : d180248 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d178208, d179091, d180248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178208, d179091, d180248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178209 q = 1) (hb : d179092 q = 1) : d180249 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d178209, d179092, d180249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178209, d179092, d180249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178210 q = 1) (hb : d179093 q = 1) : d180250 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d178210, d179093, d180250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178210, d179093, d180250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178211 q = 1) (hb : d179094 q = 1) : d180251 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d178211, d179094, d180251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178211, d179094, d180251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178212 q = 1) (hb : d179095 q = 1) : d180252 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d178212, d179095, d180252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178212, d179095, d180252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40696 (p : Pattern) (ha : d178218 p = 1) (hb : d179101 p = 1) : d180258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178213 q = 1) (hb : d179096 q = 1) : d180253 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d178213, d179096, d180253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40695 q ha hb
    | true =>
      simp only [d178213, d179096, d180253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178214 q = 1) (hb : d179097 q = 1) : d180254 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d178214, d179097, d180254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178214, d179097, d180254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178215 q = 1) (hb : d179098 q = 1) : d180255 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d178215, d179098, d180255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178215, d179098, d180255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178216 q = 1) (hb : d179099 q = 1) : d180256 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d178216, d179099, d180256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178216, d179099, d180256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178217 q = 1) (hb : d179100 q = 1) : d180257 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d178217, d179100, d180257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178217, d179100, d180257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178218 q = 1) (hb : d179101 q = 1) : d180258 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d178218, d179101, d180258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178218, d179101, d180258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40697 (p : Pattern) (ha : d178224 p = 1) (hb : d179107 p = 1) : d180264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d178219 q = 1) (hb : d179102 q = 1) : d180259 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d178219, d179102, d180259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40696 q ha hb
    | true =>
      simp only [d178219, d179102, d180259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d178220 q = 1) (hb : d179103 q = 1) : d180260 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d178220, d179103, d180260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d178220, d179103, d180260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d178221 q = 1) (hb : d179104 q = 1) : d180261 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d178221, d179104, d180261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d178221, d179104, d180261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d178222 q = 1) (hb : d179105 q = 1) : d180262 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d178222, d179105, d180262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d178222, d179105, d180262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d178223 q = 1) (hb : d179106 q = 1) : d180263 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d178223, d179106, d180263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d178223, d179106, d180263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d178224 q = 1) (hb : d179107 q = 1) : d180264 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d178224, d179107, d180264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d178224, d179107, d180264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40698 (p : Pattern) (ha : d53655 p = 1) (hb : d159762 p = 1) : d160055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
    | true =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d159762 q = 1) : d160055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40699 (p : Pattern) (ha : d53665 p = 1) (hb : d159762 p = 1) : d160092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40145 q ha hb
    | true =>
      simp only [d244, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d159762 q = 1) : d160088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d159762 q = 1) : d160089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d159762 q = 1) : d160090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d159762 q = 1) : d160091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d159762 q = 1) : d160092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40700 (p : Pattern) (ha : d53671 p = 1) (hb : d159762 p = 1) : d161043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d159762 q = 1) : d159876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40151 q ha hb
    | true =>
      simp only [d292, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40152 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d159762 q = 1) : d159877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d159762 q = 1) : d161033 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d161033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d161033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d159762 q = 1) : d161034 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d161034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d161034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d159762 q = 1) : d160056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40698 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d159762 q = 1) : d161035 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d161035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d161035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d159762 q = 1) : d161036 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d161036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d161036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d159762 q = 1) : d161037 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d161037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d161037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d159762 q = 1) : d161038 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d161038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d161038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d159762 q = 1) : d160093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40699 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d159762 q = 1) : d161039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d161039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d161039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d159762 q = 1) : d161040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d161040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d161040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d159762 q = 1) : d161041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d161041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d161041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d159762 q = 1) : d161042 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d161042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d161042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d159762 q = 1) : d161043 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d161043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d161043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40701 (p : Pattern) (ha : d53677 p = 1) (hb : d159762 p = 1) : d161049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31715 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d159762 q = 1) : d161044 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d161044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d161044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40700 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d159762 q = 1) : d161045 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d161045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d161045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d159762 q = 1) : d161046 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d161046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d161046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d159762 q = 1) : d161047 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d161047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d161047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d159762 q = 1) : d161048 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d161048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d161048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d159762 q = 1) : d161049 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d161049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d161049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40702 (p : Pattern) (ha : d159762 p = 1) (hb : d171078 p = 1) : d161052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40185 q ha hb
    | true =>
      simp only [d16052, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40176 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d159762 q = 1) : d159980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d159762 q = 1) : d159981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d159762 q = 1) : d159982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d159762 q = 1) : d159983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171078 q = 1) : d161052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d161052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171078, d161052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40703 (p : Pattern) (ha : d159762 p = 1) (hb : d171089 p = 1) : d161062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171084 q = 1) : d159955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40211 q hb ha
    | true =>
      simp only [d171084, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40180 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171085 q = 1) : d161058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d161058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171085, d161058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171086 q = 1) : d161059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d161059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d161059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171087 q = 1) : d161060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d161060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171087, d161060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171088 q = 1) : d161061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d161061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171088, d161061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171089 q = 1) : d161062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d161062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171089, d161062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40704 (p : Pattern) (ha : d159762 p = 1) (hb : d171095 p = 1) : d161068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d159762 q = 1) : d159985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40184 q ha hb
    | true =>
      simp only [d16058, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40186 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d159762 q = 1) : d159986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171076 q = 1) : d161050 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d161050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171076, d161050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171077 q = 1) : d161051 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d161051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171077, d161051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171079 q = 1) : d161053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d161053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171079, d161053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40702 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171080 q = 1) : d161054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d161054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d161054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171081 q = 1) : d161055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d161055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d161055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171082 q = 1) : d161056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d161056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d161056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171083 q = 1) : d161057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d161057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d161057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171090 q = 1) : d161063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d161063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171090, d161063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40703 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171091 q = 1) : d161064 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d161064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d161064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171092 q = 1) : d161065 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d161065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d161065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171093 q = 1) : d161066 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d161066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d161066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171094 q = 1) : d161067 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d161067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d161067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171095 q = 1) : d161068 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d161068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d161068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40705 (p : Pattern) (ha : d159762 p = 1) (hb : d171101 p = 1) : d161074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171096 q = 1) : d161069 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d161069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171096, d161069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40704 q ha hb
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171097 q = 1) : d161070 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d161070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171097, d161070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171098 q = 1) : d161071 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d161071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171098, d161071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171099 q = 1) : d161072 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d161072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171099, d161072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171100 q = 1) : d161073 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d161073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171100, d161073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171101 q = 1) : d161074 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d161074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171101, d161074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40706 (p : Pattern) (ha : d159762 p = 1) (hb : d171105 p = 1) : d180267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d159762 q = 1) : d178318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d178318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40230 q ha hb
    | true =>
      simp only [d16249, d178318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40219 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d159762 q = 1) : d178319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d178319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d178319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d159762 q = 1) : d178320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d178320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d178320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d159762 q = 1) : d178321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d178321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d178321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d159762 q = 1) : d178322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d178322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d178322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171105 q = 1) : d180267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d180267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171105, d180267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40707 (p : Pattern) (ha : d159762 p = 1) (hb : d171116 p = 1) : d180278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171111 q = 1) : d180273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d180273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40257 q hb ha
    | true =>
      simp only [d171111, d180273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40224 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171112 q = 1) : d180274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d180274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171112, d180274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171113 q = 1) : d180275 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d180275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d180275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171114 q = 1) : d180276 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d180276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171114, d180276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171115 q = 1) : d180277 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d180277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171115, d180277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171116 q = 1) : d180278 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d180278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171116, d180278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40708 (p : Pattern) (ha : d159762 p = 1) (hb : d171122 p = 1) : d180284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d159762 q = 1) : d178324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d178324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40229 q ha hb
    | true =>
      simp only [d16255, d178324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40231 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d159762 q = 1) : d178325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d178325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d178325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171103 q = 1) : d180265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d180265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171103, d180265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171104 q = 1) : d180266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d180266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171104, d180266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171106 q = 1) : d180268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d180268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171106, d180268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40706 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171107 q = 1) : d180269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d180269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d180269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171108 q = 1) : d180270 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d180270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d180270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171109 q = 1) : d180271 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d180271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d180271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171110 q = 1) : d180272 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d180272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d180272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171117 q = 1) : d180279 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d180279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171117, d180279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40707 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171118 q = 1) : d180280 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d180280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d180280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171119 q = 1) : d180281 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d180281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d180281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171120 q = 1) : d180282 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d180282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d180282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171121 q = 1) : d180283 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d180283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d180283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171122 q = 1) : d180284 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d180284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d180284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40709 (p : Pattern) (ha : d159762 p = 1) (hb : d171128 p = 1) : d180290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171123 q = 1) : d180285 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d180285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171123, d180285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40708 q ha hb
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171124 q = 1) : d180286 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d180286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171124, d180286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171125 q = 1) : d180287 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d180287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171125, d180287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171126 q = 1) : d180288 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d180288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171126, d180288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171127 q = 1) : d180289 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d180289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171127, d180289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171128 q = 1) : d180290 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d180290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171128, d180290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40710 (p : Pattern) (ha : d159762 p = 1) (hb : d171133 p = 1) : d180295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d159762 q = 1) : d178473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d178473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40271 q ha hb
    | true =>
      simp only [d16481, d178473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40272 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d159762 q = 1) : d178474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d178474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d178474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d159762 q = 1) : d178475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d178475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d178475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d159762 q = 1) : d178476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d178476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d178476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d159762 q = 1) : d178477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d178477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d178477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171133 q = 1) : d180295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d180295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171133, d180295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40711 (p : Pattern) (ha : d159762 p = 1) (hb : d171140 p = 1) : d178580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d159762 q = 1) : d178571 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40306 q ha hb
    | true =>
      simp only [d16673, d178571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d159762 q = 1) : d178572 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d178572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d159762 q = 1) : d178573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d178573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16676, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40304 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d159762 q = 1) : d178574 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d178574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40280 q ha hb
    | true =>
      simp only [d16693, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40279 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171139 q = 1) : d178579 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171139, d178579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171140 q = 1) : d178580 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d178580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40712 (p : Pattern) (ha : d159762 p = 1) (hb : d171146 p = 1) : d178590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171141 q = 1) : d178581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40711 q ha hb
    | true =>
      simp only [d171141, d178581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171142 q = 1) : d178582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171142, d178582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40281 q ha hb
    | true =>
      simp only [d16699, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171143 q = 1) : d178587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d178587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d178587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171144 q = 1) : d178588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d178588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d178588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171145 q = 1) : d178589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d178589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d178589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171146 q = 1) : d178590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d178590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d178590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40713 (p : Pattern) (ha : d159762 p = 1) (hb : d171152 p = 1) : d180306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171147 q = 1) : d180301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d180301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40712 q ha hb
    | true =>
      simp only [d171147, d180301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40282 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171148 q = 1) : d180302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d180302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171148, d180302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171149 q = 1) : d180303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d180303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d180303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171150 q = 1) : d180304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d180304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171150, d180304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171151 q = 1) : d180305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d180305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171151, d180305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171152 q = 1) : d180306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d180306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171152, d180306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40714 (p : Pattern) (ha : d159762 p = 1) (hb : d171158 p = 1) : d180312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d159762 q = 1) : d178479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d178479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40270 q ha hb
    | true =>
      simp only [d16487, d178479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40273 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d159762 q = 1) : d178480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d178480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d178480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171131 q = 1) : d180293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d180293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171131, d180293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171132 q = 1) : d180294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d180294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171132, d180294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171134 q = 1) : d180296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d180296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171134, d180296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40710 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171135 q = 1) : d180297 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d180297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d180297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171136 q = 1) : d180298 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d180298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d180298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171137 q = 1) : d180299 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d180299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d180299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171138 q = 1) : d180300 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d180300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d180300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171153 q = 1) : d180307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d180307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171153, d180307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40713 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171154 q = 1) : d180308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d180308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d180308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171155 q = 1) : d180309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d180309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d180309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171156 q = 1) : d180310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d180310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d180310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171157 q = 1) : d180311 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d180311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d180311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171158 q = 1) : d180312 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d180312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d180312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40715 (p : Pattern) (ha : d159762 p = 1) (hb : d171164 p = 1) : d180318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171159 q = 1) : d180313 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d180313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171159, d180313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40714 q ha hb
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171160 q = 1) : d180314 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d180314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171160, d180314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171161 q = 1) : d180315 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d180315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171161, d180315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171162 q = 1) : d180316 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d180316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171162, d180316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171163 q = 1) : d180317 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d180317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171163, d180317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171164 q = 1) : d180318 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d180318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171164, d180318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40716 (p : Pattern) (ha : d159762 p = 1) (hb : d171170 p = 1) : d180324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d159762 q = 1) : d178656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d178656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40326 q ha hb
    | true =>
      simp only [d16833, d178656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40327 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d159762 q = 1) : d178657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d178657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d178657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d159762 q = 1) : d178658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d178658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, d178658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d159762 q = 1) : d178659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d178659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d178659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d159762 q = 1) : d178660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d178660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d178660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171170 q = 1) : d180324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d180324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171170, d180324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40717 (p : Pattern) (ha : d159762 p = 1) (hb : d171177 p = 1) : d178789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d159762 q = 1) : d178776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40361 q ha hb
    | true =>
      simp only [d17033, d178776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d159762 q = 1) : d178777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d178777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d159762 q = 1) : d178778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d178778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17036, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40359 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d159762 q = 1) : d178782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d178782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d159762 q = 1) : d178779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40335 q ha hb
    | true =>
      simp only [d17053, d178779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40334 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d159762 q = 1) : d178780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d178780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d159762 q = 1) : d178781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d178781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d159762 q = 1) : d178787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d178787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171176 q = 1) : d178788 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171176, d178788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171177 q = 1) : d178789 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171177, d178789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40718 (p : Pattern) (ha : d159762 p = 1) (hb : d171183 p = 1) : d178803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171178 q = 1) : d178790 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40717 q ha hb
    | true =>
      simp only [d171178, d178790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171179 q = 1) : d178791 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171179, d178791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d159762 q = 1) : d178798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40336 q ha hb
    | true =>
      simp only [d17059, d178798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d159762 q = 1) : d178799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d178799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171180 q = 1) : d178800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d178800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d178800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171181 q = 1) : d178801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d178801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d178801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171182 q = 1) : d178802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d178802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d178802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171183 q = 1) : d178803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d178803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d178803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40719 (p : Pattern) (ha : d159762 p = 1) (hb : d171189 p = 1) : d180335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171184 q = 1) : d180330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d180330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40718 q ha hb
    | true =>
      simp only [d171184, d180330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40337 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171185 q = 1) : d180331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d180331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171185, d180331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171186 q = 1) : d180332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d180332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d180332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171187 q = 1) : d180333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d180333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171187, d180333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171188 q = 1) : d180334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d180334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171188, d180334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171189 q = 1) : d180335 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d180335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171189, d180335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40720 (p : Pattern) (ha : d159762 p = 1) (hb : d171195 p = 1) : d180341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d159762 q = 1) : d178662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d178662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40325 q ha hb
    | true =>
      simp only [d16839, d178662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40328 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d159762 q = 1) : d178663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d178663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d178663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171168 q = 1) : d180322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d180322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171168, d180322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171169 q = 1) : d180323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d180323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171169, d180323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171171 q = 1) : d180325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d180325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171171, d180325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40716 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171172 q = 1) : d180326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d180326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d180326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171173 q = 1) : d180327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d180327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d180327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171174 q = 1) : d180328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d180328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d180328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171175 q = 1) : d180329 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d180329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d180329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171190 q = 1) : d180336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d180336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171190, d180336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40719 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171191 q = 1) : d180337 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d180337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d180337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171192 q = 1) : d180338 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d180338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d180338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171193 q = 1) : d180339 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d180339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d180339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171194 q = 1) : d180340 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d180340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d180340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171195 q = 1) : d180341 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d180341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d180341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40721 (p : Pattern) (ha : d159762 p = 1) (hb : d171201 p = 1) : d180347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171196 q = 1) : d180342 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d180342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171196, d180342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40720 q ha hb
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171197 q = 1) : d180343 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d180343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171197, d180343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171198 q = 1) : d180344 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d180344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171198, d180344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171199 q = 1) : d180345 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d180345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171199, d180345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171200 q = 1) : d180346 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d180346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171200, d180346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171201 q = 1) : d180347 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d180347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171201, d180347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40722 (p : Pattern) (ha : d159762 p = 1) (hb : d171208 p = 1) : d180354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d159762 q = 1) : d178881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d178881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40381 q ha hb
    | true =>
      simp only [d17199, d178881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40382 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d159762 q = 1) : d178882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d178882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d178882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d159762 q = 1) : d178883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d178883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d178883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d159762 q = 1) : d178884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d178884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d178884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d159762 q = 1) : d178885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d178885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d178885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171208 q = 1) : d180354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d180354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171208, d180354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40723 (p : Pattern) (ha : d159762 p = 1) (hb : d171215 p = 1) : d179010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d159762 q = 1) : d178997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40416 q ha hb
    | true =>
      simp only [d17397, d178997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d159762 q = 1) : d178998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d178998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d159762 q = 1) : d178999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d178999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17400, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40414 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d159762 q = 1) : d179003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d179003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d159762 q = 1) : d179000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40390 q ha hb
    | true =>
      simp only [d17417, d179000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40389 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d159762 q = 1) : d179001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d179001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d159762 q = 1) : d179002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d179002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d159762 q = 1) : d179008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d179008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171214 q = 1) : d179009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171214, d179009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171215 q = 1) : d179010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d179010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40724 (p : Pattern) (ha : d159762 p = 1) (hb : d171221 p = 1) : d179024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171216 q = 1) : d179011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40723 q ha hb
    | true =>
      simp only [d171216, d179011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171217 q = 1) : d179012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171217, d179012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d159762 q = 1) : d179019 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40391 q ha hb
    | true =>
      simp only [d17423, d179019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d159762 q = 1) : d179020 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d179020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171218 q = 1) : d179021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d179021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d179021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171219 q = 1) : d179022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d179022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d179022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171220 q = 1) : d179023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d179023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d179023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171221 q = 1) : d179024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d179024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d179024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40725 (p : Pattern) (ha : d159762 p = 1) (hb : d171227 p = 1) : d180365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171222 q = 1) : d180360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d180360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40724 q ha hb
    | true =>
      simp only [d171222, d180360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40392 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171223 q = 1) : d180361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d180361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171223, d180361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171224 q = 1) : d180362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d180362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d180362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171225 q = 1) : d180363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d180363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171225, d180363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171226 q = 1) : d180364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d180364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171226, d180364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171227 q = 1) : d180365 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d180365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171227, d180365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40726 (p : Pattern) (ha : d159762 p = 1) (hb : d171233 p = 1) : d180371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d159762 q = 1) : d178887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d178887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40380 q ha hb
    | true =>
      simp only [d17205, d178887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40383 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d159762 q = 1) : d178888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d178888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d178888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171206 q = 1) : d180352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d180352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171206, d180352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171207 q = 1) : d180353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d180353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171207, d180353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171209 q = 1) : d180355 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d180355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171209, d180355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40722 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171210 q = 1) : d180356 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d180356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d180356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171211 q = 1) : d180357 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d180357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d180357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171212 q = 1) : d180358 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d180358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d180358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171213 q = 1) : d180359 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d180359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d180359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171228 q = 1) : d180366 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d180366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171228, d180366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40725 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171229 q = 1) : d180367 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d180367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d180367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171230 q = 1) : d180368 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d180368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d180368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171231 q = 1) : d180369 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d180369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d180369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171232 q = 1) : d180370 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d180370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d180370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171233 q = 1) : d180371 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d180371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d180371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40727 (p : Pattern) (ha : d159762 p = 1) (hb : d171239 p = 1) : d180377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171234 q = 1) : d180372 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d180372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171234, d180372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40726 q ha hb
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171235 q = 1) : d180373 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d180373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171235, d180373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171236 q = 1) : d180374 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d180374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171236, d180374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171237 q = 1) : d180375 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d180375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171237, d180375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171238 q = 1) : d180376 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d180376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171238, d180376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171239 q = 1) : d180377 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d180377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171239, d180377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40728 (p : Pattern) (ha : d159762 p = 1) (hb : d171245 p = 1) : d180383 p = 1 := by
  have h0 (q : Pattern) (ha : d159762 q = 1) (hb : d171102 q = 1) : d161075 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d161075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40701 q hb ha
    | true =>
      simp only [d171102, d161075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40705 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171129 q = 1) : d180291 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d180291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171129, d180291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40709 q ha hb
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171130 q = 1) : d180292 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d180292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d180292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171165 q = 1) : d180319 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d180319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171165, d180319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40715 q ha hb
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171166 q = 1) : d180320 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d180320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171166, d180320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171167 q = 1) : d180321 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d180321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d180321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159762 q = 1) (hb : d171202 q = 1) : d180348 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d180348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171202, d180348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40721 q ha hb
  have h8 (q : Pattern) (ha : d159762 q = 1) (hb : d171203 q = 1) : d180349 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d180349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171203, d180349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159762 q = 1) (hb : d171204 q = 1) : d180350 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d180350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171204, d180350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159762 q = 1) (hb : d171205 q = 1) : d180351 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d180351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d180351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d159762 q = 1) (hb : d171240 q = 1) : d180378 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d180378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171240, d180378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40727 q ha hb
  have h12 (q : Pattern) (ha : d159762 q = 1) (hb : d171241 q = 1) : d180379 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d180379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171241, d180379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d159762 q = 1) (hb : d171242 q = 1) : d180380 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d180380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171242, d180380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d159762 q = 1) (hb : d171243 q = 1) : d180381 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d180381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171243, d180381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d159762 q = 1) (hb : d171244 q = 1) : d180382 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d180382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d180382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159762 q = 1) (hb : d171245 q = 1) : d180383 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d180383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d180383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro40729 (p : Pattern) (ha : d159762 p = 1) (hb : d171251 p = 1) : d180389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171246 q = 1) : d180384 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d180384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40728 q ha hb
    | true =>
      simp only [d171246, d180384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171247 q = 1) : d180385 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d180385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d180385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171248 q = 1) : d180386 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d180386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d180386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171249 q = 1) : d180387 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d180387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d180387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171250 q = 1) : d180388 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d180388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d180388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171251 q = 1) : d180389 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d180389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d180389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40730 (p : Pattern) (ha : d159762 p = 1) (hb : d171257 p = 1) : d180395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171252 q = 1) : d180390 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d180390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40729 q ha hb
    | true =>
      simp only [d171252, d180390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171253 q = 1) : d180391 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d180391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d180391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171254 q = 1) : d180392 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d180392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d180392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171255 q = 1) : d180393 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d180393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d180393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171256 q = 1) : d180394 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d180394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d180394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171257 q = 1) : d180395 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d180395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d180395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40731 (p : Pattern) (ha : d159762 p = 1) (hb : d171263 p = 1) : d180401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171258 q = 1) : d180396 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d180396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40730 q ha hb
    | true =>
      simp only [d171258, d180396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171259 q = 1) : d180397 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d180397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d180397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171260 q = 1) : d180398 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d180398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d180398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171261 q = 1) : d180399 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d180399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d180399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171262 q = 1) : d180400 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d180400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d180400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171263 q = 1) : d180401 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d180401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d180401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40732 (p : Pattern) (ha : d159762 p = 1) (hb : d171269 p = 1) : d180407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171264 q = 1) : d180402 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d180402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40731 q ha hb
    | true =>
      simp only [d171264, d180402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171265 q = 1) : d180403 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d180403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d180403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171266 q = 1) : d180404 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d180404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d180404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171267 q = 1) : d180405 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d180405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d180405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171268 q = 1) : d180406 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d180406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d180406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171269 q = 1) : d180407 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d180407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d180407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40733 (p : Pattern) (ha : d159762 p = 1) (hb : d171275 p = 1) : d180413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171270 q = 1) : d180408 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d180408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40732 q ha hb
    | true =>
      simp only [d171270, d180408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171271 q = 1) : d180409 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d180409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d180409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171272 q = 1) : d180410 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d180410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d180410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171273 q = 1) : d180411 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d180411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d180411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171274 q = 1) : d180412 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d180412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d180412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171275 q = 1) : d180413 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d180413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d180413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40734 (p : Pattern) (ha : d159762 p = 1) (hb : d171281 p = 1) : d180419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171276 q = 1) : d180414 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d180414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40733 q ha hb
    | true =>
      simp only [d171276, d180414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171277 q = 1) : d180415 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d180415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d180415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171278 q = 1) : d180416 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d180416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d180416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171279 q = 1) : d180417 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d180417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d180417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171280 q = 1) : d180418 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d180418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d180418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171281 q = 1) : d180419 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d180419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d180419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40735 (p : Pattern) (ha : d159762 p = 1) (hb : d171287 p = 1) : d180425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159762 q = 1) (hb : d171282 q = 1) : d180420 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d180420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40734 q ha hb
    | true =>
      simp only [d171282, d180420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d159762 q = 1) (hb : d171283 q = 1) : d180421 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d180421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d180421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159762 q = 1) (hb : d171284 q = 1) : d180422 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d180422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d180422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d159762 q = 1) (hb : d171285 q = 1) : d180423 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d180423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d180423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159762 q = 1) (hb : d171286 q = 1) : d180424 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d180424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d180424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d159762 q = 1) (hb : d171287 q = 1) : d180425 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d180425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d180425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40736 (p : Pattern) (ha : d159868 p = 1) (hb : d177201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d177196 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d159864 q = 1) (hb : d177197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159864, d177197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159864, d177197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d159865 q = 1) (hb : d177198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159865, d177198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159865, d177198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159866 q = 1) (hb : d177199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159866, d177199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159866, d177199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159867 q = 1) (hb : d177200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159867, d177200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159867, d177200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159868 q = 1) (hb : d177201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159868, d177201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159868, d177201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40737 (p : Pattern) (ha : d159875 p = 1) (hb : d177208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d144194 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177196 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144116 q = 1) (hb : d159810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q ha hb
    | true =>
      simp only [d144116, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d159864 q = 1) (hb : d177197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159864, d177197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159864, d177197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d144117 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d159865 q = 1) (hb : d177198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159865, d177198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159865, d177198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159866 q = 1) (hb : d177199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159866, d177199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159866, d177199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159867 q = 1) (hb : d177200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159867, d177200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159867, d177200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d144217 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d144221 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d177203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d159871 q = 1) (hb : d177204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159871, d177204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d159871, d177204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d159872 q = 1) (hb : d177205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159872, d177205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d159872, d177205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d159873 q = 1) (hb : d177206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159873, d177206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d159873, d177206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d159874 q = 1) (hb : d177207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159874, d177207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159874, d177207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d159875 q = 1) (hb : d177208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159875, d177208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159875, d177208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40738 (p : Pattern) (ha : d160055 p = 1) (hb : d177215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144123 q = 1) (hb : d159817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q ha hb
    | true =>
      simp only [d144123, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d159871 q = 1) (hb : d177204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159871, d177204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159871, d177204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144124 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159872 q = 1) (hb : d177205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159872, d177205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159872, d177205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159873 q = 1) (hb : d177213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159873, d177213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159873, d177213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159874 q = 1) (hb : d177214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159874, d177214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159874, d177214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160055 q = 1) (hb : d177215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160055, d177215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160055, d177215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40739 (p : Pattern) (ha : d160092 p = 1) (hb : d177238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177233 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d144151 q = 1) (hb : d159847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q ha hb
    | true =>
      simp only [d144151, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d160088 q = 1) (hb : d177234 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d160088, d177234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d160088, d177234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d144152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d160089 q = 1) (hb : d177235 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d160089, d177235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d160089, d177235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d160090 q = 1) (hb : d177236 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d160090, d177236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160090, d177236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160091 q = 1) (hb : d177237 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d160091, d177237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160091, d177237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d160092 q = 1) (hb : d177238 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d160092, d177238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d160092, d177238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40740 (p : Pattern) (ha : d161043 p = 1) (hb : d177244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144182 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159876 q = 1) (hb : d177209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159876, d177209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40736 q ha hb
    | true =>
      simp only [d159876, d177209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40737 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d144231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159877 q = 1) (hb : d177210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159877, d177210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159877, d177210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161033 q = 1) (hb : d177211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161033, d177211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161033, d177211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161034 q = 1) (hb : d177212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161034, d177212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161034, d177212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d160056 q = 1) (hb : d177216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160056, d177216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160056, d177216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40738 q ha hb
  have h8 (q : Pattern) (ha : d161035 q = 1) (hb : d177217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161035, d177217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d161035, d177217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d161036 q = 1) (hb : d177218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161036, d177218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d161036, d177218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d161037 q = 1) (hb : d177219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161037, d177219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d161037, d177219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d161038 q = 1) (hb : d177220 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161038, d177220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d161038, d177220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d160093 q = 1) (hb : d177239 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d160093, d177239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d160093, d177239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40739 q ha hb
  have h13 (q : Pattern) (ha : d161039 q = 1) (hb : d177240 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161039, d177240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d161039, d177240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d161040 q = 1) (hb : d177241 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161040, d177241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d161040, d177241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d161041 q = 1) (hb : d177242 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161041, d177242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d161041, d177242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d161042 q = 1) (hb : d177243 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161042, d177243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d161042, d177243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d161043 q = 1) (hb : d177244 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d161043, d177244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d161043, d177244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro40741 (p : Pattern) (ha : d161049 p = 1) (hb : d177250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d144167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d161044 q = 1) (hb : d177245 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d161044, d177245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161044, d177245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40740 q ha hb
  have h3 (q : Pattern) (ha : d161045 q = 1) (hb : d177246 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d161045, d177246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161045, d177246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d161046 q = 1) (hb : d177247 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d161046, d177247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161046, d177247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d161047 q = 1) (hb : d177248 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d161047, d177248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161047, d177248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161048 q = 1) (hb : d177249 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d161048, d177249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161048, d177249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161049 q = 1) (hb : d177250 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d161049, d177250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161049, d177250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40742 (p : Pattern) (ha : d159977 p = 1) (hb : d177301 p = 1) : d179181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177271 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177277 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d177290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h5 (q : Pattern) (ha : d159973 q = 1) (hb : d177291 q = 1) : d179177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d177291, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159973, d177291, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d177297 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d159974 q = 1) (hb : d177298 q = 1) : d179178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d177298, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d159974, d177298, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159975 q = 1) (hb : d177299 q = 1) : d179179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d177299, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159975, d177299, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d159976 q = 1) (hb : d177300 q = 1) : d179180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d177300, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159976, d177300, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d159977 q = 1) (hb : d177301 q = 1) : d179181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159977, d177301, d179181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159977, d177301, d179181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40743 (p : Pattern) (ha : d159984 p = 1) (hb : d177320 p = 1) : d179188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177290 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159905 q = 1) (hb : d177196 q = 1) : d179122 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40455 q ha hb
    | true =>
      simp only [d159905, d177196, d179122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40437 q hb ha
  have h4 (q : Pattern) (ha : d159973 q = 1) (hb : d177291 q = 1) : d179177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159973, d177291, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d159973, d177291, d179177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d177297 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d159974 q = 1) (hb : d177298 q = 1) : d179178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159974, d177298, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d159974, d177298, d179178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159975 q = 1) (hb : d177299 q = 1) : d179179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159975, d177299, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159975, d177299, d179179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d159976 q = 1) (hb : d177300 q = 1) : d179180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159976, d177300, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159976, d177300, d179180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d177310 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d177312 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d159921 q = 1) (hb : d177203 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q ha hb
    | true =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q hb ha
  have h13 (q : Pattern) (ha : d159980 q = 1) (hb : d177313 q = 1) : d179184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159980, d177313, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d159980, d177313, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177316 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d159981 q = 1) (hb : d177317 q = 1) : d179185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159981, d177317, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d159981, d177317, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d159982 q = 1) (hb : d177318 q = 1) : d179186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159982, d177318, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d159982, d177318, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d159983 q = 1) (hb : d177319 q = 1) : d179187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159983, d177319, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d159983, d177319, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d159984 q = 1) (hb : d177320 q = 1) : d179188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d159984, d177320, d179188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d159984, d177320, d179188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40744 (p : Pattern) (ha : d161052 p = 1) (hb : d177329 p = 1) : d180428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d159921 q = 1) (hb : d177203 q = 1) : d179129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40459 q ha hb
    | true =>
      simp only [d159921, d177203, d179129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40439 q hb ha
  have h3 (q : Pattern) (ha : d159980 q = 1) (hb : d177313 q = 1) : d179184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d159980, d177313, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159980, d177313, d179184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177316 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d159981 q = 1) (hb : d177317 q = 1) : d179185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d159981, d177317, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d159981, d177317, d179185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d159982 q = 1) (hb : d177327 q = 1) : d179186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d159982, d177327, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159982, d177327, d179186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d159983 q = 1) (hb : d177328 q = 1) : d179187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d159983, d177328, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d159983, d177328, d179187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d161052 q = 1) (hb : d177329 q = 1) : d180428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d161052, d177329, d180428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161052, d177329, d180428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40745 (p : Pattern) (ha : d161062 p = 1) (hb : d177358 p = 1) : d180438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d159955 q = 1) (hb : d177233 q = 1) : d179159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d159955, d177233, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40464 q ha hb
    | true =>
      simp only [d159955, d177233, d179159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40444 q hb ha
  have h3 (q : Pattern) (ha : d161058 q = 1) (hb : d177348 q = 1) : d180434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d161058, d177348, d180434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d161058, d177348, d180434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d177354 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161059 q = 1) (hb : d177355 q = 1) : d180435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d161059, d177355, d180435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161059, d177355, d180435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161060 q = 1) (hb : d177356 q = 1) : d180436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d161060, d177356, d180436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161060, d177356, d180436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161061 q = 1) (hb : d177357 q = 1) : d180437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d161061, d177357, d180437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161061, d177357, d180437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d161062 q = 1) (hb : d177358 q = 1) : d180438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d161062, d177358, d180438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161062, d177358, d180438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40746 (p : Pattern) (ha : d161068 p = 1) (hb : d177364 p = 1) : d180444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d159985 q = 1) (hb : d177321 q = 1) : d179189 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d159985, d177321, d179189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40742 q ha hb
    | true =>
      simp only [d159985, d177321, d179189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177323 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d159986 q = 1) (hb : d177324 q = 1) : d179190 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d159986, d177324, d179190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d159986, d177324, d179190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d161050 q = 1) (hb : d177325 q = 1) : d180426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161050, d177325, d180426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d161050, d177325, d180426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161051 q = 1) (hb : d177326 q = 1) : d180427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161051, d177326, d180427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161051, d177326, d180427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d161053 q = 1) (hb : d177330 q = 1) : d180429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d161053, d177330, d180429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d161053, d177330, d180429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40744 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d144354 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d161054 q = 1) (hb : d177331 q = 1) : d180430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161054, d177331, d180430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d161054, d177331, d180430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d161055 q = 1) (hb : d177332 q = 1) : d180431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161055, d177332, d180431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d161055, d177332, d180431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d161056 q = 1) (hb : d177333 q = 1) : d180432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161056, d177333, d180432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d161056, d177333, d180432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d161057 q = 1) (hb : d177334 q = 1) : d180433 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161057, d177334, d180433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d161057, d177334, d180433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d161063 q = 1) (hb : d177359 q = 1) : d180439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d161063, d177359, d180439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d161063, d177359, d180439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40745 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d144389 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d161064 q = 1) (hb : d177360 q = 1) : d180440 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d161064, d177360, d180440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d161064, d177360, d180440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d161065 q = 1) (hb : d177361 q = 1) : d180441 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d161065, d177361, d180441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d161065, d177361, d180441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d161066 q = 1) (hb : d177362 q = 1) : d180442 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d161066, d177362, d180442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d161066, d177362, d180442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d161067 q = 1) (hb : d177363 q = 1) : d180443 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d161067, d177363, d180443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d161067, d177363, d180443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d161068 q = 1) (hb : d177364 q = 1) : d180444 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d161068, d177364, d180444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d161068, d177364, d180444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40747 (p : Pattern) (ha : d161074 p = 1) (hb : d177370 p = 1) : d180450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d161069 q = 1) (hb : d177365 q = 1) : d180445 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d161069, d177365, d180445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161069, d177365, d180445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40746 q ha hb
  have h2 (q : Pattern) (ha : d161070 q = 1) (hb : d177366 q = 1) : d180446 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d161070, d177366, d180446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161070, d177366, d180446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d161071 q = 1) (hb : d177367 q = 1) : d180447 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d161071, d177367, d180447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161071, d177367, d180447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d161072 q = 1) (hb : d177368 q = 1) : d180448 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d161072, d177368, d180448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161072, d177368, d180448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d161073 q = 1) (hb : d177369 q = 1) : d180449 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d161073, d177369, d180449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161073, d177369, d180449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d161074 q = 1) (hb : d177370 q = 1) : d180450 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d161074, d177370, d180450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d161074, d177370, d180450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40748 (p : Pattern) (ha : d177437 p = 1) (hb : d178314 p = 1) : d179317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177413 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d177426 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d177384 q = 1) (hb : d178309 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
    | true =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
  have h5 (q : Pattern) (ha : d177427 q = 1) (hb : d178310 q = 1) : d179313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177427, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d177427, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d177433 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d177434 q = 1) (hb : d178311 q = 1) : d179314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177434, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d177434, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d177435 q = 1) (hb : d178312 q = 1) : d179315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177435, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177435, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d177436 q = 1) (hb : d178313 q = 1) : d179316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177436, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177436, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d177437 q = 1) (hb : d178314 q = 1) : d179317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177437, d178314, d179317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177437, d178314, d179317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40749 (p : Pattern) (ha : d177456 p = 1) (hb : d178323 p = 1) : d179326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d177407 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d177413 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d177426 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d177384 q = 1) (hb : d178309 q = 1) : d179312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40506 q ha hb
    | true =>
      simp only [d177384, d178309, d179312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40497 q ha hb
  have h4 (q : Pattern) (ha : d177427 q = 1) (hb : d178310 q = 1) : d179313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177427, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d177427, d178310, d179313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d177433 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d177434 q = 1) (hb : d178311 q = 1) : d179314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177434, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d177434, d178311, d179314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d177435 q = 1) (hb : d178312 q = 1) : d179315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177435, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d177435, d178312, d179315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d177436 q = 1) (hb : d178313 q = 1) : d179316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177436, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d177436, d178313, d179316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d177442 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d177446 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d177448 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d177393 q = 1) (hb : d178318 q = 1) : d179321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40508 q ha hb
    | true =>
      simp only [d177393, d178318, d179321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40498 q ha hb
  have h13 (q : Pattern) (ha : d177449 q = 1) (hb : d178319 q = 1) : d179322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177449, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d177449, d178319, d179322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d177452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d177453 q = 1) (hb : d178320 q = 1) : d179323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177453, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d177453, d178320, d179323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d177454 q = 1) (hb : d178321 q = 1) : d179324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177454, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d177454, d178321, d179324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d177455 q = 1) (hb : d178322 q = 1) : d179325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177455, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d177455, d178322, d179325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d177456 q = 1) (hb : d178323 q = 1) : d179326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177456, d178323, d179326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d177456, d178323, d179326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
end NetHack.Soko22Hazard87
