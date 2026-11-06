import NetHack.Soko22Hazard87.AndIntroBlocks0120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro30250 (p : Pattern) (ha : d13156 p = 1) (hb : d152855 p = 1) : d157300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d152854 q = 1) : d157289 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d152854 q = 1) : d157113 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30205 q ha hb
    | true =>
      simp only [d1100, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d152854 q = 1) : d157290 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d152854 q = 1) : d157114 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d152854 q = 1) : d157291 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d152854 q = 1) : d157292 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d152854 q = 1) : d157295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d152854 q = 1) : d157118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30200 q ha hb
    | true =>
      simp only [d1110, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d152854 q = 1) : d157296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d152854 q = 1) : d157119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d152854 q = 1) : d157297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d152854 q = 1) : d157298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d152854 q = 1) : d157299 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d157299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d157299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13156 q = 1) (hb : d152855 q = 1) : d157300 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d152855, d157300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13156, d152855, d157300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30251 (p : Pattern) (ha : d13169 p = 1) (hb : d152855 p = 1) : d157309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d152854 q = 1) : d157304 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d157304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d157304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30232 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d152854 q = 1) : d157207 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30232 q ha hb
    | true =>
      simp only [d9814, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d152854 q = 1) : d157305 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d157305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d157305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d152854 q = 1) : d157208 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13162 q = 1) (hb : d152854 q = 1) : d157306 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d157306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13162, d157306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13163 q = 1) (hb : d152854 q = 1) : d157307 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d157307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13163, d157307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13164 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30233 q ha hb
  have h8 (q : Pattern) (ha : d13025 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30233 q ha hb
    | true =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13165 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13026 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13166 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13167 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13168 q = 1) (hb : d152854 q = 1) : d157308 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d157308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13168, d157308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13169 q = 1) (hb : d152855 q = 1) : d157309 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, d152855, d157309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13169, d152855, d157309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30252 (p : Pattern) (ha : d13179 p = 1) (hb : d152855 p = 1) : d157330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d152855 q = 1) : d157301 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d157301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30249 q ha hb
    | true =>
      simp only [d13157, d157301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30250 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d152855 q = 1) : d157302 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d157302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d157302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d152855 q = 1) : d157303 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d157303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d157303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13170 q = 1) (hb : d152855 q = 1) : d157310 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d157310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30250 q ha hb
    | true =>
      simp only [d13170, d157310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30251 q ha hb
  have h5 (q : Pattern) (ha : d13171 q = 1) (hb : d152855 q = 1) : d157311 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d157311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d157311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13172 q = 1) (hb : d152855 q = 1) : d157312 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d157312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d157312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13173 q = 1) (hb : d152855 q = 1) : d157313 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d157313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13173, d157313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13174 q = 1) (hb : d152855 q = 1) : d157320 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30250 q ha hb
    | true =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
  have h9 (q : Pattern) (ha : d13175 q = 1) (hb : d152855 q = 1) : d157321 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13176 q = 1) (hb : d152855 q = 1) : d157322 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6356 q = 1) (hb : d152855 q = 1) : d157325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
    | true =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30248 q ha hb
  have h12 (q : Pattern) (ha : d6357 q = 1) (hb : d152855 q = 1) : d157326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6358 q = 1) (hb : d152855 q = 1) : d157327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13177 q = 1) (hb : d152855 q = 1) : d157328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13178 q = 1) (hb : d152855 q = 1) : d157329 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d157329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13178, d157329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13179 q = 1) (hb : d152855 q = 1) : d157330 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d157330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13179, d157330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30253 (p : Pattern) (ha : d13183 p = 1) (hb : d152855 p = 1) : d157335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d152855 q = 1) : d157320 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30250 q ha hb
    | true =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d152855 q = 1) : d157321 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d152855 q = 1) : d157322 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d152855 q = 1) : d157325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
    | true =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30248 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d152855 q = 1) : d157326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d152855 q = 1) : d157327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d152855 q = 1) : d157328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6359 q = 1) (hb : d152855 q = 1) : d157333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6359, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13182 q = 1) (hb : d152855 q = 1) : d157334 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13182, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13183 q = 1) (hb : d152855 q = 1) : d157335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13183, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30254 (p : Pattern) (ha : d13189 p = 1) (hb : d152855 p = 1) : d157341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d152855 q = 1) : d157331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d157331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30252 q ha hb
    | true =>
      simp only [d13180, d157331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d152855 q = 1) : d157332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d157332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d157332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d152855 q = 1) : d157336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30253 q ha hb
    | true =>
      simp only [d13184, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d152855 q = 1) : d157337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d152855 q = 1) : d157338 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d157338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d157338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d152855 q = 1) : d157339 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d157339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d157339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d152855 q = 1) : d157340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d157340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d157340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d152855 q = 1) : d157341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d157341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d157341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30255 (p : Pattern) (ha : d13202 p = 1) (hb : d152855 p = 1) : d157349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d152855 q = 1) : d157336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30253 q ha hb
    | true =>
      simp only [d13184, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d152855 q = 1) : d157337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d152855 q = 1) : d157344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30223 q ha hb
    | true =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d152855 q = 1) : d157345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d152855 q = 1) : d157346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d152855 q = 1) : d157347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d152855 q = 1) : d157348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d152855 q = 1) : d157349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30256 (p : Pattern) (ha : d13243 p = 1) (hb : d152855 p = 1) : d157335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d152855 q = 1) : d157320 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30250 q ha hb
    | true =>
      simp only [d13174, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d152855 q = 1) : d157321 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d152855 q = 1) : d157322 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d152855 q = 1) : d157325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
    | true =>
      simp only [d6356, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30248 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d152855 q = 1) : d157326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d152855 q = 1) : d157327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d152855 q = 1) : d157328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13191 q = 1) (hb : d152855 q = 1) : d157325 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30221 q ha hb
    | true =>
      simp only [d13191, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30222 q ha hb
  have h9 (q : Pattern) (ha : d13192 q = 1) (hb : d152855 q = 1) : d157326 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13193 q = 1) (hb : d152855 q = 1) : d157327 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13194 q = 1) (hb : d152855 q = 1) : d157333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13194, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13242 q = 1) (hb : d152855 q = 1) : d157334 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13242, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13243 q = 1) (hb : d152855 q = 1) : d157335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13243, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30257 (p : Pattern) (ha : d13249 p = 1) (hb : d152855 p = 1) : d157355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d152855 q = 1) : d157336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30256 q ha hb
    | true =>
      simp only [d13244, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d152855 q = 1) : d157337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d152855 q = 1) : d157352 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d157352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d157352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d152855 q = 1) : d157353 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d157353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d157353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d152855 q = 1) : d157354 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d157354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d157354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d152855 q = 1) : d157355 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d157355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d157355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30258 (p : Pattern) (ha : d115422 p = 1) (hb : d152855 p = 1) : d157361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d152855 q = 1) : d157350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d157350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30254 q ha hb
    | true =>
      simp only [d13203, d157350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30255 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d152855 q = 1) : d157351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d157351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d157351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d152855 q = 1) : d157356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d157356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30257 q ha hb
    | true =>
      simp only [d13250, d157356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d152855 q = 1) : d157357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d157357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d157357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d152855 q = 1) : d157358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d157358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d157358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d152855 q = 1) : d157359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d157359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d157359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d152855 q = 1) : d157360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d157360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d157360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d152855 q = 1) : d157361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d157361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d157361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30259 (p : Pattern) (ha : d115428 p = 1) (hb : d152855 p = 1) : d157378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d152855 q = 1) : d157163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d157163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d157163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30212 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d152855 q = 1) : d157164 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d157164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d157164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d152855 q = 1) : d157173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30212 q ha hb
    | true =>
      simp only [d12998, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30215 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d152855 q = 1) : d157174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d152855 q = 1) : d157175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d157175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d157175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d152855 q = 1) : d157258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d157258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30238 q ha hb
    | true =>
      simp only [d115406, d157258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30246 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d152855 q = 1) : d157271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d157271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30218 q ha hb
    | true =>
      simp only [d13141, d157271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30219 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d152855 q = 1) : d157272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d157272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d157272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d152855 q = 1) : d157273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d157273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d157273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d152855 q = 1) : d157274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d157274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d157274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d152855 q = 1) : d157278 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d157278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d157278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30247 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d152855 q = 1) : d157280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d157280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d157280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30220 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d152855 q = 1) : d157281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d157281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d157281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d152855 q = 1) : d157282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d157282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d157282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d152855 q = 1) : d157283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d157283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d157283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d152855 q = 1) : d157284 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d157284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d157284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d152855 q = 1) : d157362 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d157362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d157362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30258 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d152855 q = 1) : d157373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d157373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d157373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30225 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d152855 q = 1) : d157374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d157374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d157374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d152855 q = 1) : d157375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d157375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d157375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d152855 q = 1) : d157376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d157376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d157376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d152855 q = 1) : d157377 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d157377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d157377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d152855 q = 1) : d157378 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d157378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d157378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30260 (p : Pattern) (ha : d115434 p = 1) (hb : d152855 p = 1) : d157384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d152855 q = 1) : d157379 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d157379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d157379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30259 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d152855 q = 1) : d157380 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d157380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d157380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d152855 q = 1) : d157381 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d157381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d157381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d152855 q = 1) : d157382 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d157382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d157382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d152855 q = 1) : d157383 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d157383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d157383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d152855 q = 1) : d157384 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d157384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d157384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30261 (p : Pattern) (ha : d1569 p = 1) (hb : d152854 p = 1) : d157393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1553 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1545 q = 1) : d1545 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1562 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1562, d152852, d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1550 q = 1) : d1550 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1566 q = 1) (hb : d152852 q = 1) : d10081 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1566, d152852, d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1567 q = 1) (hb : d152852 q = 1) : d26572 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1567, d26572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1568 q = 1) (hb : d152852 q = 1) : d26573 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1568, d26573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1569 q = 1) (hb : d152854 q = 1) : d157393 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1569, d152854, d157393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1569, d152854, d157393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30262 (p : Pattern) (ha : d1581 p = 1) (hb : d152854 p = 1) : d157402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1568 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1576 q = 1) : d1576 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1577 q = 1) (hb : d152852 q = 1) : d1593 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d152852, d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1577, d152852, d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1578 q = 1) (hb : d152852 q = 1) : d1578 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1579 q = 1) (hb : d152852 q = 1) : d157400 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1579, d157400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1579, d157400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1580 q = 1) (hb : d152852 q = 1) : d157401 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1580, d157401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1580, d157401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1581 q = 1) (hb : d152854 q = 1) : d157402 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1581, d152854, d157402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1581, d152854, d157402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30263 (p : Pattern) (ha : d5120 p = 1) (hb : d152855 p = 1) : d157408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d152854 q = 1) : d157394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
    | true =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d152854 q = 1) : d157395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d152854 q = 1) : d157396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d152854 q = 1) : d157397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d152854 q = 1) : d157403 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
    | true =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d152854 q = 1) : d157404 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d152854 q = 1) : d157405 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d152854 q = 1) : d157406 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d152854 q = 1) : d157407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d157407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d157407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5120 q = 1) (hb : d152855 q = 1) : d157408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d152855, d157408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5120, d152855, d157408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30264 (p : Pattern) (ha : d5133 p = 1) (hb : d152854 p = 1) : d157412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d5129 q = 1) : d5129 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5130 q = 1) (hb : d152852 q = 1) : d26754 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d152852, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5130, d152852, d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1578 q = 1) (hb : d152852 q = 1) : d1578 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5131 q = 1) (hb : d152852 q = 1) : d26755 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d26755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5131, d26755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5132 q = 1) (hb : d152852 q = 1) : d26756 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d26756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5132, d26756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5133 q = 1) (hb : d152854 q = 1) : d157412 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5133, d152854, d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5133, d152854, d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30265 (p : Pattern) (ha : d5139 p = 1) (hb : d152855 p = 1) : d157418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d152854 q = 1) : d157413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30264 q ha hb
    | true =>
      simp only [d5134, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d152854 q = 1) : d157414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d152854 q = 1) : d157415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d152854 q = 1) : d157416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d152854 q = 1) : d157417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5139 q = 1) (hb : d152855 q = 1) : d157418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5139, d152855, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5139, d152855, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30266 (p : Pattern) (ha : d1554 p = 1) (hb : d152854 p = 1) : d157388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1538 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1529 q = 1) : d1529 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1546 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1546, d152852, d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1535 q = 1) : d1535 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1550 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1551 q = 1) (hb : d152852 q = 1) : d26555 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1551, d152852, d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1552 q = 1) (hb : d152852 q = 1) : d26556 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1552, d26556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1553 q = 1) (hb : d152852 q = 1) : d26557 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1553, d26557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1554 q = 1) (hb : d152854 q = 1) : d157388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1554, d152854, d157388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1554, d152854, d157388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30267 (p : Pattern) (ha : d13282 p = 1) (hb : d152855 p = 1) : d157399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d152854 q = 1) : d157389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
    | true =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d152854 q = 1) : d157390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d152854 q = 1) : d157391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d152854 q = 1) : d157392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d152854 q = 1) : d157394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
    | true =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d152854 q = 1) : d157395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d152854 q = 1) : d157396 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d152854 q = 1) : d157397 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d152854 q = 1) : d157398 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d157398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d157398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13282 q = 1) (hb : d152855 q = 1) : d157399 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d152855, d157399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13282, d152855, d157399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30268 (p : Pattern) (ha : d13287 p = 1) (hb : d152855 p = 1) : d157424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d152854 q = 1) : d157403 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
    | true =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d152854 q = 1) : d157404 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d152854 q = 1) : d157405 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d152854 q = 1) : d157406 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d152854 q = 1) : d157423 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d157423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d157423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13287 q = 1) (hb : d152855 q = 1) : d157424 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d152855, d157424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d152855, d157424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30269 (p : Pattern) (ha : d13293 p = 1) (hb : d152855 p = 1) : d157430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d152855 q = 1) : d157409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30267 q ha hb
    | true =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d152855 q = 1) : d157410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d152855 q = 1) : d157411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d152855 q = 1) : d157419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
    | true =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30265 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d152855 q = 1) : d157420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d152855 q = 1) : d157421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d152855 q = 1) : d157422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13288 q = 1) (hb : d152855 q = 1) : d157425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
    | true =>
      simp only [d13288, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30268 q ha hb
  have h9 (q : Pattern) (ha : d13289 q = 1) (hb : d152855 q = 1) : d157426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13290 q = 1) (hb : d152855 q = 1) : d157427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13291 q = 1) (hb : d152855 q = 1) : d157428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13291, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13292 q = 1) (hb : d152855 q = 1) : d157429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d157429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13292, d157429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13293 q = 1) (hb : d152855 q = 1) : d157430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d157430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13293, d157430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30270 (p : Pattern) (ha : d13297 p = 1) (hb : d152855 p = 1) : d157434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13288 q = 1) (hb : d152855 q = 1) : d157425 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
    | true =>
      simp only [d13288, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30268 q ha hb
  have h2 (q : Pattern) (ha : d13289 q = 1) (hb : d152855 q = 1) : d157426 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13290 q = 1) (hb : d152855 q = 1) : d157427 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13291 q = 1) (hb : d152855 q = 1) : d157428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13291, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13296 q = 1) (hb : d152855 q = 1) : d157433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d157433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13296, d157433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13297 q = 1) (hb : d152855 q = 1) : d157434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d157434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13297, d157434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30271 (p : Pattern) (ha : d13303 p = 1) (hb : d152855 p = 1) : d157440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d152855 q = 1) : d157438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d152855 q = 1) : d157439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d152855 q = 1) : d157440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d157440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d157440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30272 (p : Pattern) (ha : d13307 p = 1) (hb : d152855 p = 1) : d157444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d152855 q = 1) : d157442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d152855 q = 1) : d157443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d152855 q = 1) : d157444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d157444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d157444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30273 (p : Pattern) (ha : d13313 p = 1) (hb : d152855 p = 1) : d157450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d152855 q = 1) : d157445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30271 q ha hb
    | true =>
      simp only [d13308, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30272 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d152855 q = 1) : d157446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d152855 q = 1) : d157447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d152855 q = 1) : d157448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d152855 q = 1) : d157449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d152855 q = 1) : d157450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30274 (p : Pattern) (ha : d13316 p = 1) (hb : d152855 p = 1) : d157453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d152855 q = 1) : d157438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d152855 q = 1) : d157439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d152855 q = 1) : d157453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d157453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d157453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30275 (p : Pattern) (ha : d13317 p = 1) (hb : d152855 p = 1) : d157454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d152855 q = 1) : d157442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d152855 q = 1) : d157443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d152855 q = 1) : d157454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d157454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d157454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30276 (p : Pattern) (ha : d13323 p = 1) (hb : d152855 p = 1) : d157460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d152855 q = 1) : d157445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30271 q ha hb
    | true =>
      simp only [d13308, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30272 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d152855 q = 1) : d157446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d152855 q = 1) : d157447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d152855 q = 1) : d157448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d152855 q = 1) : d157449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d152855 q = 1) : d157455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30274 q ha hb
    | true =>
      simp only [d13318, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30275 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d152855 q = 1) : d157456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d152855 q = 1) : d157457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d152855 q = 1) : d157458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d152855 q = 1) : d157459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d152855 q = 1) : d157460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30277 (p : Pattern) (ha : d13366 p = 1) (hb : d152855 p = 1) : d157511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d152855 q = 1) : d157409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30267 q ha hb
    | true =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d152855 q = 1) : d157410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d152855 q = 1) : d157411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d152855 q = 1) : d157419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
    | true =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30265 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d152855 q = 1) : d157420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d152855 q = 1) : d157421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d152855 q = 1) : d157422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5143 q = 1) (hb : d152855 q = 1) : d157509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d157509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5143, d157509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13365 q = 1) (hb : d152855 q = 1) : d157510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d157510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13365, d157510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13366 q = 1) (hb : d152855 q = 1) : d157511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d157511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13366, d157511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30278 (p : Pattern) (ha : d13376 p = 1) (hb : d152855 p = 1) : d157521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d152855 q = 1) : d157512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30277 q ha hb
    | true =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d152855 q = 1) : d157513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d152855 q = 1) : d157518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d152855 q = 1) : d157519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d152855 q = 1) : d157520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d152855 q = 1) : d157521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d157521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d157521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30279 (p : Pattern) (ha : d13460 p = 1) (hb : d152855 p = 1) : d157567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d152855 q = 1) : d157557 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d157557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30278 q ha hb
    | true =>
      simp only [d13450, d157557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30272 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d152855 q = 1) : d157558 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d157558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d157558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d152855 q = 1) : d157559 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d157559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d157559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d152855 q = 1) : d157560 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d157560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d157560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d152855 q = 1) : d157561 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d157561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d157561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d152855 q = 1) : d157562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30272 q ha hb
    | true =>
      simp only [d13455, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d152855 q = 1) : d157563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d152855 q = 1) : d157564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d152855 q = 1) : d157565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d152855 q = 1) : d157566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d152855 q = 1) : d157567 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d157567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d157567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30280 (p : Pattern) (ha : d13466 p = 1) (hb : d152855 p = 1) : d157573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d152855 q = 1) : d157562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30272 q ha hb
    | true =>
      simp only [d13455, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d152855 q = 1) : d157563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d152855 q = 1) : d157564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d152855 q = 1) : d157565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d152855 q = 1) : d157566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d152855 q = 1) : d157568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30275 q ha hb
    | true =>
      simp only [d13461, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d152855 q = 1) : d157569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d152855 q = 1) : d157570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d152855 q = 1) : d157571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d152855 q = 1) : d157572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d152855 q = 1) : d157573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d157573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d157573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30281 (p : Pattern) (ha : d13475 p = 1) (hb : d152855 p = 1) : d157582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d152855 q = 1) : d157568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30275 q ha hb
    | true =>
      simp only [d13461, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d152855 q = 1) : d157569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d152855 q = 1) : d157570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d152855 q = 1) : d157571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d152855 q = 1) : d157572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d152855 q = 1) : d157582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d157582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d157582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30282 (p : Pattern) (ha : d6495 p = 1) (hb : d152855 p = 1) : d157622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d152854 q = 1) : d157598 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d152854 q = 1) : d157394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
    | true =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d152854 q = 1) : d157599 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d152854 q = 1) : d157395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d152854 q = 1) : d157600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d152854 q = 1) : d157601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d152854 q = 1) : d157617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d152854 q = 1) : d157403 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
    | true =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d152854 q = 1) : d157618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d152854 q = 1) : d157404 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d152854 q = 1) : d157619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d152854 q = 1) : d157620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d152854 q = 1) : d157621 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d157621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d157621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6495 q = 1) (hb : d152855 q = 1) : d157622 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d152855, d157622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6495, d152855, d157622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30283 (p : Pattern) (ha : d13516 p = 1) (hb : d152855 p = 1) : d157650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d152854 q = 1) : d157617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d152854 q = 1) : d157403 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30262 q ha hb
    | true =>
      simp only [d1582, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d152854 q = 1) : d157618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d152854 q = 1) : d157404 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d152854 q = 1) : d157619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d152854 q = 1) : d157620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d152854 q = 1) : d157649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d157649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d157649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d152855 q = 1) : d157650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d152855, d157650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, d152855, d157650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30284 (p : Pattern) (ha : d13522 p = 1) (hb : d152855 p = 1) : d157656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13517 q = 1) (hb : d152855 q = 1) : d157651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
    | true =>
      simp only [d13517, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30283 q ha hb
  have h2 (q : Pattern) (ha : d13518 q = 1) (hb : d152855 q = 1) : d157652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13519 q = 1) (hb : d152855 q = 1) : d157653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13520 q = 1) (hb : d152855 q = 1) : d157654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13520, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13521 q = 1) (hb : d152855 q = 1) : d157655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d157655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13521, d157655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13522 q = 1) (hb : d152855 q = 1) : d157656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d157656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13522, d157656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30285 (p : Pattern) (ha : d13586 p = 1) (hb : d152855 p = 1) : d157683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d152855 q = 1) : d157657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30284 q ha hb
    | true =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d152855 q = 1) : d157658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d152855 q = 1) : d157680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d157680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d157680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d152855 q = 1) : d157681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d157681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d157681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d152855 q = 1) : d157682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d157682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d157682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d152855 q = 1) : d157683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d157683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d157683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30286 (p : Pattern) (ha : d13592 p = 1) (hb : d152855 p = 1) : d157689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d152855 q = 1) : d157684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d157684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30285 q ha hb
    | true =>
      simp only [d13587, d157684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d152855 q = 1) : d157685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d157685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d157685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d152855 q = 1) : d157686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d157686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d157686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d152855 q = 1) : d157687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d157687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d157687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d152855 q = 1) : d157688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d157688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d157688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d152855 q = 1) : d157689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d157689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d157689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30287 (p : Pattern) (ha : d13328 p = 1) (hb : d152855 p = 1) : d157465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d152855 q = 1) : d157438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d152855 q = 1) : d157464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d152855 q = 1) : d157465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d157465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d157465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30288 (p : Pattern) (ha : d13330 p = 1) (hb : d152855 p = 1) : d157467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d152855 q = 1) : d157442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d152855 q = 1) : d157466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d152855 q = 1) : d157467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d157467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d157467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30289 (p : Pattern) (ha : d13337 p = 1) (hb : d152855 p = 1) : d157474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d152855 q = 1) : d157472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d152855 q = 1) : d157473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d152855 q = 1) : d157474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d157474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d157474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30290 (p : Pattern) (ha : d13340 p = 1) (hb : d152855 p = 1) : d157477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d152855 q = 1) : d157475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d152855 q = 1) : d157476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d152855 q = 1) : d157477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d157477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d157477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30291 (p : Pattern) (ha : d1664 p = 1) (hb : d152854 p = 1) : d157481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1201 q = 1) : d1201 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1530 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1530, d152852, d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d1205 q = 1) : d1205 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1535 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1536 q = 1) (hb : d152852 q = 1) : d26185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d1536, d152852, d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1537 q = 1) (hb : d152852 q = 1) : d26186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1537, d26186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1538 q = 1) (hb : d152852 q = 1) : d26187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1538, d26187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1664 q = 1) (hb : d152854 q = 1) : d157481 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1664, d152854, d157481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1664, d152854, d157481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30292 (p : Pattern) (ha : d13344 p = 1) (hb : d152855 p = 1) : d157487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d152854 q = 1) : d157482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30291 q ha hb
    | true =>
      simp only [d1665, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d152854 q = 1) : d157483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d152854 q = 1) : d157484 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d157484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d157484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d152854 q = 1) : d157485 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d157485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d157485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1555 q = 1) (hb : d152854 q = 1) : d157389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
    | true =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1556 q = 1) (hb : d152854 q = 1) : d157390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1557 q = 1) (hb : d152854 q = 1) : d157391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1558 q = 1) (hb : d152854 q = 1) : d157392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1558, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1669 q = 1) (hb : d152854 q = 1) : d157486 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d157486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1669, d157486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13344 q = 1) (hb : d152855 q = 1) : d157487 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d152855, d157487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13344, d152855, d157487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30293 (p : Pattern) (ha : d10098 p = 1) (hb : d152854 p = 1) : d157494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d10056 q = 1) : d10056 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10058 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10059 q = 1) (hb : d152852 q = 1) : d157491 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10059, d152852, d157491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d10059, d152852, d157491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10060 q = 1) (hb : d152852 q = 1) : d157492 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10060, d157492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10060, d157492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10061 q = 1) (hb : d152852 q = 1) : d157493 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10061, d157493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10061, d157493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d10098 q = 1) (hb : d152854 q = 1) : d157494 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10098, d152854, d157494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10098, d152854, d157494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30294 (p : Pattern) (ha : d13350 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13350 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13350, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30295 (p : Pattern) (ha : d13356 p = 1) (hb : d152855 p = 1) : d157500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d152854 q = 1) : d157495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30293 q ha hb
    | true =>
      simp only [d10099, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d152854 q = 1) : d157496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d152854 q = 1) : d157497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d157497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d157497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d152854 q = 1) : d157498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d157498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d157498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13351 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30294 q ha hb
    | true =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13352 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13353 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13354 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13355 q = 1) (hb : d152854 q = 1) : d157499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d157499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13355, d157499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13356 q = 1) (hb : d152855 q = 1) : d157500 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, d152855, d157500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13356, d152855, d157500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30296 (p : Pattern) (ha : d13362 p = 1) (hb : d152855 p = 1) : d157506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d152855 q = 1) : d157488 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d157488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30292 q ha hb
    | true =>
      simp only [d13345, d157488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30267 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d152855 q = 1) : d157489 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d157489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d157489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d152855 q = 1) : d157490 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d157490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d157490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13357 q = 1) (hb : d152855 q = 1) : d157501 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d157501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30267 q ha hb
    | true =>
      simp only [d13357, d157501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30295 q ha hb
  have h5 (q : Pattern) (ha : d13358 q = 1) (hb : d152855 q = 1) : d157502 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d157502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d157502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13359 q = 1) (hb : d152855 q = 1) : d157503 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d157503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d157503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13360 q = 1) (hb : d152855 q = 1) : d157504 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d157504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13360, d157504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13283 q = 1) (hb : d152855 q = 1) : d157409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30267 q ha hb
    | true =>
      simp only [d13283, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
  have h9 (q : Pattern) (ha : d13284 q = 1) (hb : d152855 q = 1) : d157410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13285 q = 1) (hb : d152855 q = 1) : d157411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5140 q = 1) (hb : d152855 q = 1) : d157419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30263 q ha hb
    | true =>
      simp only [d5140, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30265 q ha hb
  have h12 (q : Pattern) (ha : d5141 q = 1) (hb : d152855 q = 1) : d157420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5142 q = 1) (hb : d152855 q = 1) : d157421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13286 q = 1) (hb : d152855 q = 1) : d157422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13286, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13361 q = 1) (hb : d152855 q = 1) : d157505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d157505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13361, d157505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13362 q = 1) (hb : d152855 q = 1) : d157506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d157506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13362, d157506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30297 (p : Pattern) (ha : d13372 p = 1) (hb : d152855 p = 1) : d157517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d152855 q = 1) : d157507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30296 q ha hb
    | true =>
      simp only [d13363, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d152855 q = 1) : d157508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d152855 q = 1) : d157512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30277 q ha hb
    | true =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d152855 q = 1) : d157513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d152855 q = 1) : d157514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d152855 q = 1) : d157515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d152855 q = 1) : d157516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d152855 q = 1) : d157517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d157517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d157517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30298 (p : Pattern) (ha : d13417 p = 1) (hb : d152855 p = 1) : d157527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d152855 q = 1) : d157524 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d152855 q = 1) : d157525 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d152855 q = 1) : d157526 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d152855 q = 1) : d157527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d157527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d157527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30299 (p : Pattern) (ha : d115442 p = 1) (hb : d152855 p = 1) : d157533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d152855 q = 1) : d157468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30287 q ha hb
    | true =>
      simp only [d13331, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30288 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d152855 q = 1) : d157469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d152855 q = 1) : d157470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d152855 q = 1) : d157471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d152855 q = 1) : d157478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30289 q ha hb
    | true =>
      simp only [d13341, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30290 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d152855 q = 1) : d157479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d152855 q = 1) : d157480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d152855 q = 1) : d157522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30297 q ha hb
    | true =>
      simp only [d13377, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30278 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d152855 q = 1) : d157523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d152855 q = 1) : d157528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30298 q ha hb
    | true =>
      simp only [d13418, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d152855 q = 1) : d157529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d152855 q = 1) : d157530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d152855 q = 1) : d157531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d152855 q = 1) : d157532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d152855 q = 1) : d157533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d157533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d157533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30300 (p : Pattern) (ha : d13424 p = 1) (hb : d152855 p = 1) : d157534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d152855 q = 1) : d157438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d152855 q = 1) : d157464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d152855 q = 1) : d157534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d157534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d157534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30301 (p : Pattern) (ha : d13425 p = 1) (hb : d152855 p = 1) : d157535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d152855 q = 1) : d157442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d152855 q = 1) : d157466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d152855 q = 1) : d157535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, d157535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, d157535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30302 (p : Pattern) (ha : d13430 p = 1) (hb : d152855 p = 1) : d157540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d152855 q = 1) : d157437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d152855 q = 1) : d157472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d152855 q = 1) : d157473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13430 q = 1) (hb : d152855 q = 1) : d157540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d157540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13430, d157540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30303 (p : Pattern) (ha : d13431 p = 1) (hb : d152855 p = 1) : d157541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d152855 q = 1) : d157441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d152855 q = 1) : d157475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d152855 q = 1) : d157476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d152855 q = 1) : d157541 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, d157541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, d157541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30304 (p : Pattern) (ha : d13435 p = 1) (hb : d152855 p = 1) : d157545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d152855 q = 1) : d157507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30296 q ha hb
    | true =>
      simp only [d13363, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d152855 q = 1) : d157508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d152855 q = 1) : d157512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30277 q ha hb
    | true =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d152855 q = 1) : d157513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d152855 q = 1) : d157514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d152855 q = 1) : d157515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d152855 q = 1) : d157516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d152855 q = 1) : d157545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d157545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d157545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30305 (p : Pattern) (ha : d13436 p = 1) (hb : d152855 p = 1) : d157546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d152855 q = 1) : d157512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30277 q ha hb
    | true =>
      simp only [d13367, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d152855 q = 1) : d157513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d152855 q = 1) : d157435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30270 q ha hb
    | true =>
      simp only [d13298, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d152855 q = 1) : d157436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d152855 q = 1) : d157518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d152855 q = 1) : d157519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d152855 q = 1) : d157520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13436 q = 1) (hb : d152855 q = 1) : d157546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d157546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13436, d157546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30306 (p : Pattern) (ha : d13442 p = 1) (hb : d152855 p = 1) : d157549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d152855 q = 1) : d157431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30269 q ha hb
    | true =>
      simp only [d13294, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d152855 q = 1) : d157432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d152855 q = 1) : d157524 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d152855 q = 1) : d157525 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d152855 q = 1) : d157526 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d152855 q = 1) : d157549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d157549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d157549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30307 (p : Pattern) (ha : d115447 p = 1) (hb : d152855 p = 1) : d157555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d152855 q = 1) : d157468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30287 q ha hb
    | true =>
      simp only [d13331, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30288 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d152855 q = 1) : d157469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d152855 q = 1) : d157470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d152855 q = 1) : d157471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d152855 q = 1) : d157478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30289 q ha hb
    | true =>
      simp only [d13341, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30290 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d152855 q = 1) : d157479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d152855 q = 1) : d157480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d152855 q = 1) : d157522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30297 q ha hb
    | true =>
      simp only [d13377, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30278 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d152855 q = 1) : d157523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d152855 q = 1) : d157528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30298 q ha hb
    | true =>
      simp only [d13418, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d152855 q = 1) : d157529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d152855 q = 1) : d157530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d152855 q = 1) : d157531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d152855 q = 1) : d157532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13426 q = 1) (hb : d152855 q = 1) : d157536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d157536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30300 q ha hb
    | true =>
      simp only [d13426, d157536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30301 q ha hb
  have h16 (q : Pattern) (ha : d13427 q = 1) (hb : d152855 q = 1) : d157537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d157537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d157537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13428 q = 1) (hb : d152855 q = 1) : d157538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d157538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13428, d157538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13429 q = 1) (hb : d152855 q = 1) : d157539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d157539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d157539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13432 q = 1) (hb : d152855 q = 1) : d157542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d157542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30302 q ha hb
    | true =>
      simp only [d13432, d157542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30303 q ha hb
  have h20 (q : Pattern) (ha : d13433 q = 1) (hb : d152855 q = 1) : d157543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d157543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d157543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13434 q = 1) (hb : d152855 q = 1) : d157544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d157544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13434, d157544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13437 q = 1) (hb : d152855 q = 1) : d157547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30304 q ha hb
    | true =>
      simp only [d13437, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30305 q ha hb
  have h23 (q : Pattern) (ha : d115443 q = 1) (hb : d152855 q = 1) : d157548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115443, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13443 q = 1) (hb : d152855 q = 1) : d157550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30306 q ha hb
    | true =>
      simp only [d13443, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13444 q = 1) (hb : d152855 q = 1) : d157551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13444, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115444 q = 1) (hb : d152855 q = 1) : d157552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115444, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115445 q = 1) (hb : d152855 q = 1) : d157553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d157553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115445, d157553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115446 q = 1) (hb : d152855 q = 1) : d157554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d157554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115446, d157554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115447 q = 1) (hb : d152855 q = 1) : d157555 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d157555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115447, d157555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30308 (p : Pattern) (ha : d115454 p = 1) (hb : d152855 p = 1) : d157580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d152855 q = 1) : d157547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30304 q ha hb
    | true =>
      simp only [d13437, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30305 q ha hb
  have h2 (q : Pattern) (ha : d115443 q = 1) (hb : d152855 q = 1) : d157548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115443, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d152855 q = 1) : d157550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30306 q ha hb
    | true =>
      simp only [d13443, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d152855 q = 1) : d157551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d152855 q = 1) : d157552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d152855 q = 1) : d157578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d157578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d157578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d152855 q = 1) : d157579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d157579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d157579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d152855 q = 1) : d157580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d157580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d157580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30309 (p : Pattern) (ha : d6501 p = 1) (hb : d152855 p = 1) : d157631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d152854 q = 1) : d157626 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30264 q ha hb
  have h2 (q : Pattern) (ha : d5134 q = 1) (hb : d152854 q = 1) : d157413 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30264 q ha hb
    | true =>
      simp only [d5134, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6497 q = 1) (hb : d152854 q = 1) : d157627 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6497, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5135 q = 1) (hb : d152854 q = 1) : d157414 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5135, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6498 q = 1) (hb : d152854 q = 1) : d157628 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6498, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6499 q = 1) (hb : d152854 q = 1) : d157629 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6499, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6500 q = 1) (hb : d152854 q = 1) : d157630 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6501 q = 1) (hb : d152855 q = 1) : d157631 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d152855, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6501, d152855, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30310 (p : Pattern) (ha : d13481 p = 1) (hb : d152855 p = 1) : d157597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d152854 q = 1) : d157588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d157588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d157588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30291 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d152854 q = 1) : d157482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30291 q ha hb
    | true =>
      simp only [d1665, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d152854 q = 1) : d157589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d157589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d157589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d152854 q = 1) : d157483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d152854 q = 1) : d157590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d157590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d157590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d152854 q = 1) : d157591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d157591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d157591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1857 q = 1) (hb : d152854 q = 1) : d157592 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
  have h8 (q : Pattern) (ha : d1555 q = 1) (hb : d152854 q = 1) : d157389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
    | true =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1858 q = 1) (hb : d152854 q = 1) : d157593 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1858, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1556 q = 1) (hb : d152854 q = 1) : d157390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1859 q = 1) (hb : d152854 q = 1) : d157594 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1859, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1860 q = 1) (hb : d152854 q = 1) : d157595 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1860, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1861 q = 1) (hb : d152854 q = 1) : d157596 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d157596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1861, d157596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13481 q = 1) (hb : d152855 q = 1) : d157597 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13481, d152855, d157597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13481, d152855, d157597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30311 (p : Pattern) (ha : d13482 p = 1) (hb : d152855 p = 1) : d157603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d152854 q = 1) : d157592 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d152854 q = 1) : d157389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30266 q ha hb
    | true =>
      simp only [d1555, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d152854 q = 1) : d157593 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d152854 q = 1) : d157390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d152854 q = 1) : d157594 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d152854 q = 1) : d157595 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1862 q = 1) (hb : d152854 q = 1) : d157598 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
  have h8 (q : Pattern) (ha : d1570 q = 1) (hb : d152854 q = 1) : d157394 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30261 q ha hb
    | true =>
      simp only [d1570, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1863 q = 1) (hb : d152854 q = 1) : d157599 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1863, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1571 q = 1) (hb : d152854 q = 1) : d157395 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1571, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1864 q = 1) (hb : d152854 q = 1) : d157600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1864, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1865 q = 1) (hb : d152854 q = 1) : d157601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1865, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1866 q = 1) (hb : d152854 q = 1) : d157602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d157602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1866, d157602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13482 q = 1) (hb : d152855 q = 1) : d157603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, d152855, d157603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13482, d152855, d157603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30312 (p : Pattern) (ha : d13495 p = 1) (hb : d152855 p = 1) : d157612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d152854 q = 1) : d157607 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d157607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d157607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30293 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d152854 q = 1) : d157495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30293 q ha hb
    | true =>
      simp only [d10099, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d152854 q = 1) : d157608 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d157608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d157608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d152854 q = 1) : d157496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13488 q = 1) (hb : d152854 q = 1) : d157609 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d157609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13488, d157609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d152854 q = 1) : d157610 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d157610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13489, d157610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30294 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30294 q ha hb
    | true =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13494 q = 1) (hb : d152854 q = 1) : d157611 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d157611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13494, d157611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13495 q = 1) (hb : d152855 q = 1) : d157612 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, d152855, d157612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13495, d152855, d157612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30313 (p : Pattern) (ha : d13505 p = 1) (hb : d152855 p = 1) : d157637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13483 q = 1) (hb : d152855 q = 1) : d157604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d157604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30310 q ha hb
    | true =>
      simp only [d13483, d157604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30311 q ha hb
  have h2 (q : Pattern) (ha : d13484 q = 1) (hb : d152855 q = 1) : d157605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d157605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d157605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13485 q = 1) (hb : d152855 q = 1) : d157606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d157606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d157606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13496 q = 1) (hb : d152855 q = 1) : d157613 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, d157613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30311 q ha hb
    | true =>
      simp only [d13496, d157613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30312 q ha hb
  have h5 (q : Pattern) (ha : d13497 q = 1) (hb : d152855 q = 1) : d157614 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, d157614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13497, d157614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13498 q = 1) (hb : d152855 q = 1) : d157615 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, d157615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13498, d157615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13499 q = 1) (hb : d152855 q = 1) : d157616 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d157616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13499, d157616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13500 q = 1) (hb : d152855 q = 1) : d157623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30311 q ha hb
    | true =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
  have h9 (q : Pattern) (ha : d13501 q = 1) (hb : d152855 q = 1) : d157624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13502 q = 1) (hb : d152855 q = 1) : d157625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6502 q = 1) (hb : d152855 q = 1) : d157632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
    | true =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30309 q ha hb
  have h12 (q : Pattern) (ha : d6503 q = 1) (hb : d152855 q = 1) : d157633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6504 q = 1) (hb : d152855 q = 1) : d157634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13503 q = 1) (hb : d152855 q = 1) : d157635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13504 q = 1) (hb : d152855 q = 1) : d157636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d157636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13504, d157636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13505 q = 1) (hb : d152855 q = 1) : d157637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d157637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13505, d157637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30314 (p : Pattern) (ha : d13509 p = 1) (hb : d152855 p = 1) : d157642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d152855 q = 1) : d157623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30311 q ha hb
    | true =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d152855 q = 1) : d157624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d152855 q = 1) : d157625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d152855 q = 1) : d157632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
    | true =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30309 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d152855 q = 1) : d157633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d152855 q = 1) : d157634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d152855 q = 1) : d157635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6505 q = 1) (hb : d152855 q = 1) : d157640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d157640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6505, d157640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13508 q = 1) (hb : d152855 q = 1) : d157641 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d157641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13508, d157641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13509 q = 1) (hb : d152855 q = 1) : d157642 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d157642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13509, d157642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30315 (p : Pattern) (ha : d13515 p = 1) (hb : d152855 p = 1) : d157648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d152855 q = 1) : d157638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d157638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30313 q ha hb
    | true =>
      simp only [d13506, d157638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d152855 q = 1) : d157639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d157639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d157639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d152855 q = 1) : d157643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30314 q ha hb
    | true =>
      simp only [d13510, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d152855 q = 1) : d157644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d152855 q = 1) : d157645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d157645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d157645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d152855 q = 1) : d157646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d157646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d157646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d152855 q = 1) : d157647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d157647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d157647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d152855 q = 1) : d157648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d157648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d157648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30316 (p : Pattern) (ha : d13528 p = 1) (hb : d152855 p = 1) : d157662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d152855 q = 1) : d157643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30314 q ha hb
    | true =>
      simp only [d13510, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d152855 q = 1) : d157644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d152855 q = 1) : d157657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30284 q ha hb
    | true =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d152855 q = 1) : d157658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13525 q = 1) (hb : d152855 q = 1) : d157659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d157659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d157659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13526 q = 1) (hb : d152855 q = 1) : d157660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d157660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13526, d157660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13527 q = 1) (hb : d152855 q = 1) : d157661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d157661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13527, d157661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13528 q = 1) (hb : d152855 q = 1) : d157662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d157662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13528, d157662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30317 (p : Pattern) (ha : d13569 p = 1) (hb : d152855 p = 1) : d157666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d152855 q = 1) : d157623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30311 q ha hb
    | true =>
      simp only [d13500, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d152855 q = 1) : d157624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d152855 q = 1) : d157625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d152855 q = 1) : d157632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
    | true =>
      simp only [d6502, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30309 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d152855 q = 1) : d157633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d152855 q = 1) : d157634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d152855 q = 1) : d157635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13517 q = 1) (hb : d152855 q = 1) : d157651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30282 q ha hb
    | true =>
      simp only [d13517, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30283 q ha hb
  have h9 (q : Pattern) (ha : d13518 q = 1) (hb : d152855 q = 1) : d157652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13519 q = 1) (hb : d152855 q = 1) : d157653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13520 q = 1) (hb : d152855 q = 1) : d157654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13520, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13568 q = 1) (hb : d152855 q = 1) : d157665 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d157665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13568, d157665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13569 q = 1) (hb : d152855 q = 1) : d157666 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d157666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13569, d157666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30318 (p : Pattern) (ha : d13575 p = 1) (hb : d152855 p = 1) : d157672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d152855 q = 1) : d157667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30317 q ha hb
    | true =>
      simp only [d13570, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d152855 q = 1) : d157668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d152855 q = 1) : d157669 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d157669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d157669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d152855 q = 1) : d157670 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d157670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d157670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d152855 q = 1) : d157671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d157671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d157671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d152855 q = 1) : d157672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d157672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d157672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30319 (p : Pattern) (ha : d115464 p = 1) (hb : d152855 p = 1) : d157678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d152855 q = 1) : d157663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d157663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30315 q ha hb
    | true =>
      simp only [d13529, d157663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30316 q ha hb
  have h2 (q : Pattern) (ha : d115460 q = 1) (hb : d152855 q = 1) : d157664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d157664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115460, d157664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d152855 q = 1) : d157673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d157673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30318 q ha hb
    | true =>
      simp only [d13576, d157673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d152855 q = 1) : d157674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d157674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d157674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d152855 q = 1) : d157675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d157675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d157675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d152855 q = 1) : d157676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d157676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d157676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d152855 q = 1) : d157677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d157677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d157677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d152855 q = 1) : d157678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d157678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d157678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30320 (p : Pattern) (ha : d115470 p = 1) (hb : d152855 p = 1) : d157695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d152855 q = 1) : d157451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d157451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d157451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30273 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d152855 q = 1) : d157452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d157452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d157452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d152855 q = 1) : d157461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30273 q ha hb
    | true =>
      simp only [d13324, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30276 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d152855 q = 1) : d157462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d152855 q = 1) : d157463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d157463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d157463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115448 q = 1) (hb : d152855 q = 1) : d157556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d157556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30299 q ha hb
    | true =>
      simp only [d115448, d157556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30307 q ha hb
  have h7 (q : Pattern) (ha : d13467 q = 1) (hb : d152855 q = 1) : d157574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d157574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30279 q ha hb
    | true =>
      simp only [d13467, d157574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30280 q ha hb
  have h8 (q : Pattern) (ha : d115449 q = 1) (hb : d152855 q = 1) : d157575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d157575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d157575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115450 q = 1) (hb : d152855 q = 1) : d157576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d157576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115450, d157576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115451 q = 1) (hb : d152855 q = 1) : d157577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d157577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115451, d157577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115455 q = 1) (hb : d152855 q = 1) : d157581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d157581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115455, d157581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30308 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d152855 q = 1) : d157583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d157583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d157583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30281 q ha hb
  have h13 (q : Pattern) (ha : d115456 q = 1) (hb : d152855 q = 1) : d157584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d157584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115456, d157584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115457 q = 1) (hb : d152855 q = 1) : d157585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d157585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115457, d157585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115458 q = 1) (hb : d152855 q = 1) : d157586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d157586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115458, d157586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115459 q = 1) (hb : d152855 q = 1) : d157587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d157587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115459, d157587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115465 q = 1) (hb : d152855 q = 1) : d157679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d157679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115465, d157679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30319 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d152855 q = 1) : d157690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d157690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d157690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30286 q ha hb
  have h19 (q : Pattern) (ha : d115466 q = 1) (hb : d152855 q = 1) : d157691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d157691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115466, d157691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115467 q = 1) (hb : d152855 q = 1) : d157692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d157692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115467, d157692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115468 q = 1) (hb : d152855 q = 1) : d157693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d157693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115468, d157693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115469 q = 1) (hb : d152855 q = 1) : d157694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d157694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115469, d157694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115470 q = 1) (hb : d152855 q = 1) : d157695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d157695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115470, d157695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30321 (p : Pattern) (ha : d115476 p = 1) (hb : d152855 p = 1) : d157701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d152855 q = 1) : d157696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d157696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d157696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30320 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d152855 q = 1) : d157697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d157697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d157697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d152855 q = 1) : d157698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d157698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d157698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d152855 q = 1) : d157699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d157699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d157699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d152855 q = 1) : d157700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d157700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d157700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d152855 q = 1) : d157701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d157701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d157701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30322 (p : Pattern) (ha : d2052 p = 1) (hb : d152854 p = 1) : d157706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2025 q = 1) : d2025 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2045 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2045, d152852, d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d2030 q = 1) : d2030 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2049 q = 1) (hb : d152852 q = 1) : d27032 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d2049, d152852, d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2050 q = 1) (hb : d152852 q = 1) : d27033 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2050, d27033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2051 q = 1) (hb : d152852 q = 1) : d27034 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2051, d27034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2052 q = 1) (hb : d152854 q = 1) : d157706 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2052, d152854, d157706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2052, d152854, d157706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30323 (p : Pattern) (ha : d2064 p = 1) (hb : d152854 p = 1) : d157715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2059 q = 1) : d2059 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2060 q = 1) (hb : d152852 q = 1) : d2076 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d152852, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2060, d152852, d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2061 q = 1) (hb : d152852 q = 1) : d2061 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2062 q = 1) (hb : d152852 q = 1) : d157713 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2062, d157713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2062, d157713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2063 q = 1) (hb : d152852 q = 1) : d157714 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2063, d157714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2063, d157714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2064 q = 1) (hb : d152854 q = 1) : d157715 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2064, d152854, d157715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2064, d152854, d157715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30324 (p : Pattern) (ha : d5237 p = 1) (hb : d152855 p = 1) : d157721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d152854 q = 1) : d157707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
    | true =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d152854 q = 1) : d157708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d152854 q = 1) : d157709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d152854 q = 1) : d157710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2065 q = 1) (hb : d152854 q = 1) : d157716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
    | true =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2066 q = 1) (hb : d152854 q = 1) : d157717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2067 q = 1) (hb : d152854 q = 1) : d157718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2068 q = 1) (hb : d152854 q = 1) : d157719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2068, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2069 q = 1) (hb : d152854 q = 1) : d157720 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d157720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2069, d157720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5237 q = 1) (hb : d152855 q = 1) : d157721 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d152855, d157721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5237, d152855, d157721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30325 (p : Pattern) (ha : d5246 p = 1) (hb : d152854 p = 1) : d157725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5242 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d5239 q = 1) : d5239 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5243 q = 1) (hb : d152852 q = 1) : d27181 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d152852, d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5243, d152852, d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2061 q = 1) (hb : d152852 q = 1) : d2061 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5244 q = 1) (hb : d152852 q = 1) : d27182 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d27182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5244, d27182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5245 q = 1) (hb : d152852 q = 1) : d27183 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d27183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5245, d27183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5246 q = 1) (hb : d152854 q = 1) : d157725 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5246, d152854, d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5246, d152854, d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30326 (p : Pattern) (ha : d5252 p = 1) (hb : d152855 p = 1) : d157731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d152854 q = 1) : d157726 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30325 q ha hb
    | true =>
      simp only [d5247, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5248 q = 1) (hb : d152854 q = 1) : d157727 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5248, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5249 q = 1) (hb : d152854 q = 1) : d157728 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d152854 q = 1) : d157729 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5250, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d152854 q = 1) : d157730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5252 q = 1) (hb : d152855 q = 1) : d157731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5252, d152855, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5252, d152855, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30327 (p : Pattern) (ha : d2034 p = 1) (hb : d152854 p = 1) : d27014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2012 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2009 q = 1) : d2009 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2026 q = 1) (hb : d152852 q = 1) : d10349 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2026, d152852, d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2030 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2031 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2031, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2032 q = 1) (hb : d152852 q = 1) : d10350 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2032, d10350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2033 q = 1) (hb : d152852 q = 1) : d10351 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2033, d10351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2034 q = 1) (hb : d152854 q = 1) : d27014 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2034, d152854, d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2034, d152854, d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30328 (p : Pattern) (ha : d13609 p = 1) (hb : d152855 p = 1) : d157712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d152854 q = 1) : d27015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
    | true =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d152854 q = 1) : d27016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d152854 q = 1) : d27017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d27017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d27017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d152854 q = 1) : d27018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d27018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d27018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2053 q = 1) (hb : d152854 q = 1) : d157707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
    | true =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2054 q = 1) (hb : d152854 q = 1) : d157708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2055 q = 1) (hb : d152854 q = 1) : d157709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2056 q = 1) (hb : d152854 q = 1) : d157710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2056, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2057 q = 1) (hb : d152854 q = 1) : d157711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d157711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2057, d157711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13609 q = 1) (hb : d152855 q = 1) : d157712 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, d152855, d157712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13609, d152855, d157712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30329 (p : Pattern) (ha : d13614 p = 1) (hb : d152855 p = 1) : d157737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d152854 q = 1) : d157716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
    | true =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d152854 q = 1) : d157717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d152854 q = 1) : d157718 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d152854 q = 1) : d157719 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d152854 q = 1) : d157736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d157736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d157736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13614 q = 1) (hb : d152855 q = 1) : d157737 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d152855, d157737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, d152855, d157737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30330 (p : Pattern) (ha : d13620 p = 1) (hb : d152855 p = 1) : d157743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d152855 q = 1) : d157722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30328 q ha hb
    | true =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d152855 q = 1) : d157723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d152855 q = 1) : d157724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d152855 q = 1) : d157732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
    | true =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30326 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d152855 q = 1) : d157733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d152855 q = 1) : d157734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d152855 q = 1) : d157735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13615 q = 1) (hb : d152855 q = 1) : d157738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
    | true =>
      simp only [d13615, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30329 q ha hb
  have h9 (q : Pattern) (ha : d13616 q = 1) (hb : d152855 q = 1) : d157739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13617 q = 1) (hb : d152855 q = 1) : d157740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13618 q = 1) (hb : d152855 q = 1) : d157741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13618, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13619 q = 1) (hb : d152855 q = 1) : d157742 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d157742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13619, d157742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13620 q = 1) (hb : d152855 q = 1) : d157743 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d157743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13620, d157743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30331 (p : Pattern) (ha : d13624 p = 1) (hb : d152855 p = 1) : d157747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13615 q = 1) (hb : d152855 q = 1) : d157738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
    | true =>
      simp only [d13615, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30329 q ha hb
  have h2 (q : Pattern) (ha : d13616 q = 1) (hb : d152855 q = 1) : d157739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13617 q = 1) (hb : d152855 q = 1) : d157740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13618 q = 1) (hb : d152855 q = 1) : d157741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13618, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13623 q = 1) (hb : d152855 q = 1) : d157746 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, d157746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13623, d157746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13624 q = 1) (hb : d152855 q = 1) : d157747 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, d157747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13624, d157747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30332 (p : Pattern) (ha : d13630 p = 1) (hb : d152855 p = 1) : d157753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d152855 q = 1) : d157751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d152855 q = 1) : d157752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13630 q = 1) (hb : d152855 q = 1) : d157753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d157753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d157753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30333 (p : Pattern) (ha : d13634 p = 1) (hb : d152855 p = 1) : d157757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d152855 q = 1) : d157755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d152855 q = 1) : d157756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d152855 q = 1) : d157757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, d157757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, d157757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30334 (p : Pattern) (ha : d13640 p = 1) (hb : d152855 p = 1) : d157763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d152855 q = 1) : d157758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30332 q ha hb
    | true =>
      simp only [d13635, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30333 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d152855 q = 1) : d157759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d152855 q = 1) : d157760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d152855 q = 1) : d157761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d152855 q = 1) : d157762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13640 q = 1) (hb : d152855 q = 1) : d157763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30335 (p : Pattern) (ha : d13643 p = 1) (hb : d152855 p = 1) : d157766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d152855 q = 1) : d157751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d152855 q = 1) : d157752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13643 q = 1) (hb : d152855 q = 1) : d157766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d157766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13643, d157766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30336 (p : Pattern) (ha : d13644 p = 1) (hb : d152855 p = 1) : d157767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d152855 q = 1) : d157755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d152855 q = 1) : d157756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d152855 q = 1) : d157767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, d157767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, d157767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30337 (p : Pattern) (ha : d13650 p = 1) (hb : d152855 p = 1) : d157773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d152855 q = 1) : d157758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30332 q ha hb
    | true =>
      simp only [d13635, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30333 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d152855 q = 1) : d157759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d152855 q = 1) : d157760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d152855 q = 1) : d157761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d152855 q = 1) : d157762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13645 q = 1) (hb : d152855 q = 1) : d157768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30335 q ha hb
    | true =>
      simp only [d13645, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30336 q ha hb
  have h7 (q : Pattern) (ha : d13646 q = 1) (hb : d152855 q = 1) : d157769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13647 q = 1) (hb : d152855 q = 1) : d157770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13647, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13648 q = 1) (hb : d152855 q = 1) : d157771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13649 q = 1) (hb : d152855 q = 1) : d157772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13650 q = 1) (hb : d152855 q = 1) : d157773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13650, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30338 (p : Pattern) (ha : d13693 p = 1) (hb : d152855 p = 1) : d157808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d152855 q = 1) : d157722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30328 q ha hb
    | true =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d152855 q = 1) : d157723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d152855 q = 1) : d157724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d152855 q = 1) : d157732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
    | true =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30326 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d152855 q = 1) : d157733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d152855 q = 1) : d157734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d152855 q = 1) : d157735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5256 q = 1) (hb : d152855 q = 1) : d157806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d157806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5256, d157806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13692 q = 1) (hb : d152855 q = 1) : d157807 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d157807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13692, d157807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13693 q = 1) (hb : d152855 q = 1) : d157808 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d157808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13693, d157808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30339 (p : Pattern) (ha : d13703 p = 1) (hb : d152855 p = 1) : d157818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d152855 q = 1) : d157809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30338 q ha hb
    | true =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d152855 q = 1) : d157810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d152855 q = 1) : d157815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d152855 q = 1) : d157816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d152855 q = 1) : d157817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13703 q = 1) (hb : d152855 q = 1) : d157818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d157818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d157818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30340 (p : Pattern) (ha : d13787 p = 1) (hb : d152855 p = 1) : d157864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13777 q = 1) (hb : d152855 q = 1) : d157854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d157854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30339 q ha hb
    | true =>
      simp only [d13777, d157854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30333 q ha hb
  have h2 (q : Pattern) (ha : d13778 q = 1) (hb : d152855 q = 1) : d157855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d157855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d157855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13779 q = 1) (hb : d152855 q = 1) : d157856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d157856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13779, d157856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13780 q = 1) (hb : d152855 q = 1) : d157857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d157857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d157857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13781 q = 1) (hb : d152855 q = 1) : d157858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d157858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d157858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d152855 q = 1) : d157859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30333 q ha hb
    | true =>
      simp only [d13782, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d152855 q = 1) : d157860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d152855 q = 1) : d157861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d152855 q = 1) : d157862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d152855 q = 1) : d157863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13787 q = 1) (hb : d152855 q = 1) : d157864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d157864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13787, d157864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30341 (p : Pattern) (ha : d13793 p = 1) (hb : d152855 p = 1) : d157870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d152855 q = 1) : d157859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30333 q ha hb
    | true =>
      simp only [d13782, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d152855 q = 1) : d157860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d152855 q = 1) : d157861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d152855 q = 1) : d157862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d152855 q = 1) : d157863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d152855 q = 1) : d157865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30336 q ha hb
    | true =>
      simp only [d13788, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d152855 q = 1) : d157866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d152855 q = 1) : d157867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d152855 q = 1) : d157868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d152855 q = 1) : d157869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d152855 q = 1) : d157870 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, d157870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, d157870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30342 (p : Pattern) (ha : d13802 p = 1) (hb : d152855 p = 1) : d157879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d152855 q = 1) : d157865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30336 q ha hb
    | true =>
      simp only [d13788, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d152855 q = 1) : d157866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d152855 q = 1) : d157867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d152855 q = 1) : d157868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d152855 q = 1) : d157869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d152855 q = 1) : d157879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, d157879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, d157879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30343 (p : Pattern) (ha : d6642 p = 1) (hb : d152855 p = 1) : d157904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d152854 q = 1) : d157886 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d152854 q = 1) : d157707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
    | true =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d152854 q = 1) : d157887 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d152854 q = 1) : d157708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d152854 q = 1) : d157888 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d152854 q = 1) : d157889 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2346 q = 1) (hb : d152854 q = 1) : d157899 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
  have h8 (q : Pattern) (ha : d2065 q = 1) (hb : d152854 q = 1) : d157716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
    | true =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2347 q = 1) (hb : d152854 q = 1) : d157900 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2347, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2066 q = 1) (hb : d152854 q = 1) : d157717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2348 q = 1) (hb : d152854 q = 1) : d157901 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2348, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2349 q = 1) (hb : d152854 q = 1) : d157902 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2349, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2350 q = 1) (hb : d152854 q = 1) : d157903 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d157903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2350, d157903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6642 q = 1) (hb : d152855 q = 1) : d157904 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d152855, d157904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6642, d152855, d157904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30344 (p : Pattern) (ha : d13843 p = 1) (hb : d152855 p = 1) : d157932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d152854 q = 1) : d157899 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d152854 q = 1) : d157716 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30323 q ha hb
    | true =>
      simp only [d2065, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d152854 q = 1) : d157900 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d152854 q = 1) : d157717 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d152854 q = 1) : d157901 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d152854 q = 1) : d157902 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d152854 q = 1) : d157931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d157931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d157931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d152855 q = 1) : d157932 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d152855, d157932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, d152855, d157932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30345 (p : Pattern) (ha : d13849 p = 1) (hb : d152855 p = 1) : d157938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13844 q = 1) (hb : d152855 q = 1) : d157933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
    | true =>
      simp only [d13844, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30344 q ha hb
  have h2 (q : Pattern) (ha : d13845 q = 1) (hb : d152855 q = 1) : d157934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13846 q = 1) (hb : d152855 q = 1) : d157935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13847 q = 1) (hb : d152855 q = 1) : d157936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13847, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13848 q = 1) (hb : d152855 q = 1) : d157937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, d157937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13848, d157937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13849 q = 1) (hb : d152855 q = 1) : d157938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, d157938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13849, d157938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30346 (p : Pattern) (ha : d13913 p = 1) (hb : d152855 p = 1) : d157965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d152855 q = 1) : d157939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30345 q ha hb
    | true =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d152855 q = 1) : d157940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d152855 q = 1) : d157962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, d157962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, d157962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d152855 q = 1) : d157963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, d157963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, d157963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d152855 q = 1) : d157964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, d157964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, d157964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d152855 q = 1) : d157965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, d157965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, d157965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30347 (p : Pattern) (ha : d13919 p = 1) (hb : d152855 p = 1) : d157971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d152855 q = 1) : d157966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, d157966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30346 q ha hb
    | true =>
      simp only [d13914, d157966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d152855 q = 1) : d157967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, d157967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, d157967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d152855 q = 1) : d157968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, d157968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, d157968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d152855 q = 1) : d157969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, d157969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, d157969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d152855 q = 1) : d157970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, d157970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, d157970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d152855 q = 1) : d157971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, d157971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, d157971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30348 (p : Pattern) (ha : d13655 p = 1) (hb : d152855 p = 1) : d157778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d152855 q = 1) : d157751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d152855 q = 1) : d157777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13655 q = 1) (hb : d152855 q = 1) : d157778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d157778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d157778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30349 (p : Pattern) (ha : d13657 p = 1) (hb : d152855 p = 1) : d157780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d152855 q = 1) : d157755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d152855 q = 1) : d157779 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d152855 q = 1) : d157780 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, d157780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, d157780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30350 (p : Pattern) (ha : d13664 p = 1) (hb : d152855 p = 1) : d157787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d152855 q = 1) : d157785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d152855 q = 1) : d157786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13664 q = 1) (hb : d152855 q = 1) : d157787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d157787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d157787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30351 (p : Pattern) (ha : d13667 p = 1) (hb : d152855 p = 1) : d157790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d152855 q = 1) : d157788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d152855 q = 1) : d157789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d152855 q = 1) : d157790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, d157790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, d157790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30352 (p : Pattern) (ha : d2143 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2010 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2010, d152852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2011 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2012 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d2143 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2143, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2143, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30353 (p : Pattern) (ha : d13671 p = 1) (hb : d152855 p = 1) : d157794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30352 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2035 q = 1) (hb : d152854 q = 1) : d27015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
    | true =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2036 q = 1) (hb : d152854 q = 1) : d27016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2037 q = 1) (hb : d152854 q = 1) : d27017 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d27017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d27017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2038 q = 1) (hb : d152854 q = 1) : d27018 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d27018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2038, d27018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2148 q = 1) (hb : d152854 q = 1) : d27105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2148, d27105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2148, d27105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13671 q = 1) (hb : d152855 q = 1) : d157794 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13671, d152855, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13671, d152855, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30354 (p : Pattern) (ha : d10352 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10352 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10352, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10352, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30355 (p : Pattern) (ha : d13677 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13677 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13677, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro30356 (p : Pattern) (ha : d13683 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30354 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30355 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13683 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13683, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30357 (p : Pattern) (ha : d13689 p = 1) (hb : d152855 p = 1) : d157803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13672 q = 1) (hb : d152855 q = 1) : d157795 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, d157795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30353 q ha hb
    | true =>
      simp only [d13672, d157795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30328 q ha hb
  have h2 (q : Pattern) (ha : d13673 q = 1) (hb : d152855 q = 1) : d157796 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, d157796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13673, d157796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13674 q = 1) (hb : d152855 q = 1) : d157797 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, d157797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13674, d157797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13684 q = 1) (hb : d152855 q = 1) : d157798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, d157798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30328 q ha hb
    | true =>
      simp only [d13684, d157798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30356 q ha hb
  have h5 (q : Pattern) (ha : d13685 q = 1) (hb : d152855 q = 1) : d157799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, d157799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13685, d157799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13686 q = 1) (hb : d152855 q = 1) : d157800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, d157800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13686, d157800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13687 q = 1) (hb : d152855 q = 1) : d157801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d157801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13687, d157801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13610 q = 1) (hb : d152855 q = 1) : d157722 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30328 q ha hb
    | true =>
      simp only [d13610, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
  have h9 (q : Pattern) (ha : d13611 q = 1) (hb : d152855 q = 1) : d157723 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13612 q = 1) (hb : d152855 q = 1) : d157724 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5253 q = 1) (hb : d152855 q = 1) : d157732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30324 q ha hb
    | true =>
      simp only [d5253, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30326 q ha hb
  have h12 (q : Pattern) (ha : d5254 q = 1) (hb : d152855 q = 1) : d157733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5255 q = 1) (hb : d152855 q = 1) : d157734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13613 q = 1) (hb : d152855 q = 1) : d157735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13613, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13688 q = 1) (hb : d152855 q = 1) : d157802 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d157802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13688, d157802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13689 q = 1) (hb : d152855 q = 1) : d157803 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d157803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13689, d157803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30358 (p : Pattern) (ha : d13699 p = 1) (hb : d152855 p = 1) : d157814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d152855 q = 1) : d157804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30357 q ha hb
    | true =>
      simp only [d13690, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d152855 q = 1) : d157805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d152855 q = 1) : d157809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30338 q ha hb
    | true =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d152855 q = 1) : d157810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d152855 q = 1) : d157811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d152855 q = 1) : d157812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d152855 q = 1) : d157813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d152855 q = 1) : d157814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d157814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d157814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30359 (p : Pattern) (ha : d13744 p = 1) (hb : d152855 p = 1) : d157824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d152855 q = 1) : d157821 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d152855 q = 1) : d157822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d152855 q = 1) : d157823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d152855 q = 1) : d157824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d157824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d157824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30360 (p : Pattern) (ha : d115485 p = 1) (hb : d152855 p = 1) : d157830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d152855 q = 1) : d157781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30348 q ha hb
    | true =>
      simp only [d13658, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30349 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d152855 q = 1) : d157782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d152855 q = 1) : d157783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d152855 q = 1) : d157784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d152855 q = 1) : d157791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30350 q ha hb
    | true =>
      simp only [d13668, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30351 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d152855 q = 1) : d157792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d152855 q = 1) : d157793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d152855 q = 1) : d157819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30358 q ha hb
    | true =>
      simp only [d13704, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30339 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d152855 q = 1) : d157820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d152855 q = 1) : d157825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30359 q ha hb
    | true =>
      simp only [d13745, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d152855 q = 1) : d157826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d152855 q = 1) : d157827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d152855 q = 1) : d157828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d152855 q = 1) : d157829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115485 q = 1) (hb : d152855 q = 1) : d157830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d157830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d157830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30361 (p : Pattern) (ha : d13751 p = 1) (hb : d152855 p = 1) : d157831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d152855 q = 1) : d157751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d152855 q = 1) : d157777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13751 q = 1) (hb : d152855 q = 1) : d157831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d157831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13751, d157831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30362 (p : Pattern) (ha : d13752 p = 1) (hb : d152855 p = 1) : d157832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d152855 q = 1) : d157755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d152855 q = 1) : d157779 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13752 q = 1) (hb : d152855 q = 1) : d157832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, d157832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13752, d157832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30363 (p : Pattern) (ha : d13757 p = 1) (hb : d152855 p = 1) : d157837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d152855 q = 1) : d157750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d152855 q = 1) : d157785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d152855 q = 1) : d157786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13757 q = 1) (hb : d152855 q = 1) : d157837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d157837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13757, d157837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30364 (p : Pattern) (ha : d13758 p = 1) (hb : d152855 p = 1) : d157838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d152855 q = 1) : d157754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d152855 q = 1) : d157788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d152855 q = 1) : d157789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13758 q = 1) (hb : d152855 q = 1) : d157838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, d157838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13758, d157838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30365 (p : Pattern) (ha : d13762 p = 1) (hb : d152855 p = 1) : d157842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d152855 q = 1) : d157804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30357 q ha hb
    | true =>
      simp only [d13690, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d152855 q = 1) : d157805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d152855 q = 1) : d157809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30338 q ha hb
    | true =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d152855 q = 1) : d157810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d152855 q = 1) : d157811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d152855 q = 1) : d157812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d152855 q = 1) : d157813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d152855 q = 1) : d157842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d157842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d157842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30366 (p : Pattern) (ha : d13763 p = 1) (hb : d152855 p = 1) : d157843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d152855 q = 1) : d157809 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30338 q ha hb
    | true =>
      simp only [d13694, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d152855 q = 1) : d157810 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d152855 q = 1) : d157748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30331 q ha hb
    | true =>
      simp only [d13625, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d152855 q = 1) : d157749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d152855 q = 1) : d157815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d152855 q = 1) : d157816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d152855 q = 1) : d157817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13763 q = 1) (hb : d152855 q = 1) : d157843 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d157843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13763, d157843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30367 (p : Pattern) (ha : d13769 p = 1) (hb : d152855 p = 1) : d157846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d152855 q = 1) : d157744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30330 q ha hb
    | true =>
      simp only [d13621, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d152855 q = 1) : d157745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d152855 q = 1) : d157821 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d152855 q = 1) : d157822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d152855 q = 1) : d157823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d152855 q = 1) : d157846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d157846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d157846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30368 (p : Pattern) (ha : d115490 p = 1) (hb : d152855 p = 1) : d157852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d152855 q = 1) : d157781 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30348 q ha hb
    | true =>
      simp only [d13658, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30349 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d152855 q = 1) : d157782 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d152855 q = 1) : d157783 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d152855 q = 1) : d157784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d152855 q = 1) : d157791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30350 q ha hb
    | true =>
      simp only [d13668, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30351 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d152855 q = 1) : d157792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d152855 q = 1) : d157793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d152855 q = 1) : d157819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30358 q ha hb
    | true =>
      simp only [d13704, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30339 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d152855 q = 1) : d157820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d152855 q = 1) : d157825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30359 q ha hb
    | true =>
      simp only [d13745, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d152855 q = 1) : d157826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d152855 q = 1) : d157827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d152855 q = 1) : d157828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d152855 q = 1) : d157829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13753 q = 1) (hb : d152855 q = 1) : d157833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d157833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30361 q ha hb
    | true =>
      simp only [d13753, d157833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30362 q ha hb
  have h16 (q : Pattern) (ha : d13754 q = 1) (hb : d152855 q = 1) : d157834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d157834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d157834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13755 q = 1) (hb : d152855 q = 1) : d157835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d157835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13755, d157835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13756 q = 1) (hb : d152855 q = 1) : d157836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d157836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d157836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13759 q = 1) (hb : d152855 q = 1) : d157839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d157839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30363 q ha hb
    | true =>
      simp only [d13759, d157839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30364 q ha hb
  have h20 (q : Pattern) (ha : d13760 q = 1) (hb : d152855 q = 1) : d157840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d157840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d157840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13761 q = 1) (hb : d152855 q = 1) : d157841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d157841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13761, d157841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13764 q = 1) (hb : d152855 q = 1) : d157844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30365 q ha hb
    | true =>
      simp only [d13764, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30366 q ha hb
  have h23 (q : Pattern) (ha : d115486 q = 1) (hb : d152855 q = 1) : d157845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115486, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13770 q = 1) (hb : d152855 q = 1) : d157847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30367 q ha hb
    | true =>
      simp only [d13770, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13771 q = 1) (hb : d152855 q = 1) : d157848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13771, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115487 q = 1) (hb : d152855 q = 1) : d157849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115487, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115488 q = 1) (hb : d152855 q = 1) : d157850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d157850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115488, d157850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115489 q = 1) (hb : d152855 q = 1) : d157851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d157851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115489, d157851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115490 q = 1) (hb : d152855 q = 1) : d157852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d157852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115490, d157852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30369 (p : Pattern) (ha : d115497 p = 1) (hb : d152855 p = 1) : d157877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d152855 q = 1) : d157844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30365 q ha hb
    | true =>
      simp only [d13764, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30366 q ha hb
  have h2 (q : Pattern) (ha : d115486 q = 1) (hb : d152855 q = 1) : d157845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115486, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d152855 q = 1) : d157847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30367 q ha hb
    | true =>
      simp only [d13770, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d152855 q = 1) : d157848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d152855 q = 1) : d157849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d152855 q = 1) : d157875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d157875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d157875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d152855 q = 1) : d157876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d157876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d157876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d152855 q = 1) : d157877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d157877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d157877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30370 (p : Pattern) (ha : d6648 p = 1) (hb : d152855 p = 1) : d157913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d152854 q = 1) : d157908 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30325 q ha hb
  have h2 (q : Pattern) (ha : d5247 q = 1) (hb : d152854 q = 1) : d157726 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30325 q ha hb
    | true =>
      simp only [d5247, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6644 q = 1) (hb : d152854 q = 1) : d157909 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6644, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5248 q = 1) (hb : d152854 q = 1) : d157727 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5248, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6645 q = 1) (hb : d152854 q = 1) : d157910 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6645, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6646 q = 1) (hb : d152854 q = 1) : d157911 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6646, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6647 q = 1) (hb : d152854 q = 1) : d157912 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d6648 q = 1) (hb : d152855 q = 1) : d157913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d152855, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6648, d152855, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30371 (p : Pattern) (ha : d13808 p = 1) (hb : d152855 p = 1) : d157885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30352 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30352 q ha hb
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2335 q = 1) (hb : d152854 q = 1) : d27267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d27267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d27267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
  have h8 (q : Pattern) (ha : d2035 q = 1) (hb : d152854 q = 1) : d27015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
    | true =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2336 q = 1) (hb : d152854 q = 1) : d27268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d27268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2336, d27268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2036 q = 1) (hb : d152854 q = 1) : d27016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2337 q = 1) (hb : d152854 q = 1) : d27269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d27269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2337, d27269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2338 q = 1) (hb : d152854 q = 1) : d27270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d27270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2338, d27270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2339 q = 1) (hb : d152854 q = 1) : d27271 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, d27271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2339, d27271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13808 q = 1) (hb : d152855 q = 1) : d157885 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13808, d152855, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13808, d152855, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30372 (p : Pattern) (ha : d13809 p = 1) (hb : d152855 p = 1) : d157891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d152854 q = 1) : d27267 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d27267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d27267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d152854 q = 1) : d27015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30327 q ha hb
    | true =>
      simp only [d2035, d27015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d152854 q = 1) : d27268 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d27268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d27268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d152854 q = 1) : d27016 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d27016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d152854 q = 1) : d27269 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d27269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, d27269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d152854 q = 1) : d27270 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d27270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, d27270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2340 q = 1) (hb : d152854 q = 1) : d157886 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
  have h8 (q : Pattern) (ha : d2053 q = 1) (hb : d152854 q = 1) : d157707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30322 q ha hb
    | true =>
      simp only [d2053, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2341 q = 1) (hb : d152854 q = 1) : d157887 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2341, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2054 q = 1) (hb : d152854 q = 1) : d157708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2054, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2342 q = 1) (hb : d152854 q = 1) : d157888 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2342, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2343 q = 1) (hb : d152854 q = 1) : d157889 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2343, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2344 q = 1) (hb : d152854 q = 1) : d157890 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d157890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2344, d157890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13809 q = 1) (hb : d152855 q = 1) : d157891 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13809, d152855, d157891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13809, d152855, d157891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30373 (p : Pattern) (ha : d13822 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30354 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30354 q ha hb
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30355 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30355 q ha hb
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13822 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13822, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30374 (p : Pattern) (ha : d13832 p = 1) (hb : d152855 p = 1) : d157919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13810 q = 1) (hb : d152855 q = 1) : d157892 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, d157892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30371 q ha hb
    | true =>
      simp only [d13810, d157892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30372 q ha hb
  have h2 (q : Pattern) (ha : d13811 q = 1) (hb : d152855 q = 1) : d157893 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, d157893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13811, d157893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13812 q = 1) (hb : d152855 q = 1) : d157894 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, d157894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13812, d157894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13823 q = 1) (hb : d152855 q = 1) : d157895 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, d157895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30372 q ha hb
    | true =>
      simp only [d13823, d157895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30373 q ha hb
  have h5 (q : Pattern) (ha : d13824 q = 1) (hb : d152855 q = 1) : d157896 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, d157896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13824, d157896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13825 q = 1) (hb : d152855 q = 1) : d157897 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, d157897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13825, d157897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13826 q = 1) (hb : d152855 q = 1) : d157898 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d157898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13826, d157898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13827 q = 1) (hb : d152855 q = 1) : d157905 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30372 q ha hb
    | true =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
  have h9 (q : Pattern) (ha : d13828 q = 1) (hb : d152855 q = 1) : d157906 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13829 q = 1) (hb : d152855 q = 1) : d157907 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6649 q = 1) (hb : d152855 q = 1) : d157914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
    | true =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30370 q ha hb
  have h12 (q : Pattern) (ha : d6650 q = 1) (hb : d152855 q = 1) : d157915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6651 q = 1) (hb : d152855 q = 1) : d157916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13830 q = 1) (hb : d152855 q = 1) : d157917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13831 q = 1) (hb : d152855 q = 1) : d157918 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d157918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13831, d157918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13832 q = 1) (hb : d152855 q = 1) : d157919 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d157919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13832, d157919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro30375 (p : Pattern) (ha : d13836 p = 1) (hb : d152855 p = 1) : d157924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d152855 q = 1) : d157905 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30372 q ha hb
    | true =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d152855 q = 1) : d157906 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d152855 q = 1) : d157907 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d152855 q = 1) : d157914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
    | true =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30370 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d152855 q = 1) : d157915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d152855 q = 1) : d157916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d152855 q = 1) : d157917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6652 q = 1) (hb : d152855 q = 1) : d157922 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d157922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6652, d157922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13835 q = 1) (hb : d152855 q = 1) : d157923 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d157923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13835, d157923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13836 q = 1) (hb : d152855 q = 1) : d157924 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d157924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13836, d157924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro30376 (p : Pattern) (ha : d13842 p = 1) (hb : d152855 p = 1) : d157930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d152855 q = 1) : d157920 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d157920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30374 q ha hb
    | true =>
      simp only [d13833, d157920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d152855 q = 1) : d157921 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d157921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d157921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d152855 q = 1) : d157925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30375 q ha hb
    | true =>
      simp only [d13837, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d152855 q = 1) : d157926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d152855 q = 1) : d157927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d157927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d157927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d152855 q = 1) : d157928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d157928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d157928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d152855 q = 1) : d157929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d157929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d157929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d152855 q = 1) : d157930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d157930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d157930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30377 (p : Pattern) (ha : d13855 p = 1) (hb : d152855 p = 1) : d157944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d152855 q = 1) : d157925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30375 q ha hb
    | true =>
      simp only [d13837, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d152855 q = 1) : d157926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d152855 q = 1) : d157939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30345 q ha hb
    | true =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d152855 q = 1) : d157940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13852 q = 1) (hb : d152855 q = 1) : d157941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d157941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d157941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13853 q = 1) (hb : d152855 q = 1) : d157942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d157942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13853, d157942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13854 q = 1) (hb : d152855 q = 1) : d157943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d157943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13854, d157943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13855 q = 1) (hb : d152855 q = 1) : d157944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d157944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13855, d157944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30378 (p : Pattern) (ha : d13896 p = 1) (hb : d152855 p = 1) : d157948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d152855 q = 1) : d157905 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30372 q ha hb
    | true =>
      simp only [d13827, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d152855 q = 1) : d157906 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d152855 q = 1) : d157907 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d152855 q = 1) : d157914 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
    | true =>
      simp only [d6649, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30370 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d152855 q = 1) : d157915 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d152855 q = 1) : d157916 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d152855 q = 1) : d157917 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13844 q = 1) (hb : d152855 q = 1) : d157933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30343 q ha hb
    | true =>
      simp only [d13844, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30344 q ha hb
  have h9 (q : Pattern) (ha : d13845 q = 1) (hb : d152855 q = 1) : d157934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13846 q = 1) (hb : d152855 q = 1) : d157935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13847 q = 1) (hb : d152855 q = 1) : d157936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13847, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13895 q = 1) (hb : d152855 q = 1) : d157947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d157947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13895, d157947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13896 q = 1) (hb : d152855 q = 1) : d157948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d157948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13896, d157948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro30379 (p : Pattern) (ha : d13902 p = 1) (hb : d152855 p = 1) : d157954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d152855 q = 1) : d157949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30378 q ha hb
    | true =>
      simp only [d13897, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d152855 q = 1) : d157950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d152855 q = 1) : d157951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d157951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d157951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d152855 q = 1) : d157952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d157952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d157952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d152855 q = 1) : d157953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d157953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d157953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d152855 q = 1) : d157954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d157954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d157954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30380 (p : Pattern) (ha : d115507 p = 1) (hb : d152855 p = 1) : d157960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d152855 q = 1) : d157945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d157945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30376 q ha hb
    | true =>
      simp only [d13856, d157945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30377 q ha hb
  have h2 (q : Pattern) (ha : d115503 q = 1) (hb : d152855 q = 1) : d157946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d157946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115503, d157946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d152855 q = 1) : d157955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d157955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30379 q ha hb
    | true =>
      simp only [d13903, d157955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d152855 q = 1) : d157956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d157956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d157956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d152855 q = 1) : d157957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d157957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d157957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d152855 q = 1) : d157958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d157958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d157958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d152855 q = 1) : d157959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d157959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d157959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d152855 q = 1) : d157960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d157960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d157960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30381 (p : Pattern) (ha : d115513 p = 1) (hb : d152855 p = 1) : d157977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d152855 q = 1) : d157764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d157764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d157764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30334 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d152855 q = 1) : d157765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d157765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d157765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d152855 q = 1) : d157774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30334 q ha hb
    | true =>
      simp only [d13651, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30337 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d152855 q = 1) : d157775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d152855 q = 1) : d157776 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d157776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d157776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115491 q = 1) (hb : d152855 q = 1) : d157853 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d157853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30360 q ha hb
    | true =>
      simp only [d115491, d157853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30368 q ha hb
  have h7 (q : Pattern) (ha : d13794 q = 1) (hb : d152855 q = 1) : d157871 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d157871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30340 q ha hb
    | true =>
      simp only [d13794, d157871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30341 q ha hb
  have h8 (q : Pattern) (ha : d115492 q = 1) (hb : d152855 q = 1) : d157872 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d157872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d157872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115493 q = 1) (hb : d152855 q = 1) : d157873 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d157873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115493, d157873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115494 q = 1) (hb : d152855 q = 1) : d157874 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d157874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115494, d157874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115498 q = 1) (hb : d152855 q = 1) : d157878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d157878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115498, d157878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30369 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d152855 q = 1) : d157880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, d157880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, d157880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30342 q ha hb
  have h13 (q : Pattern) (ha : d115499 q = 1) (hb : d152855 q = 1) : d157881 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d157881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115499, d157881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115500 q = 1) (hb : d152855 q = 1) : d157882 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d157882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115500, d157882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115501 q = 1) (hb : d152855 q = 1) : d157883 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d157883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115501, d157883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115502 q = 1) (hb : d152855 q = 1) : d157884 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d157884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115502, d157884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115508 q = 1) (hb : d152855 q = 1) : d157961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d157961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115508, d157961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30380 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d152855 q = 1) : d157972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, d157972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, d157972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30347 q ha hb
  have h19 (q : Pattern) (ha : d115509 q = 1) (hb : d152855 q = 1) : d157973 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d157973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115509, d157973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115510 q = 1) (hb : d152855 q = 1) : d157974 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d157974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115510, d157974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115511 q = 1) (hb : d152855 q = 1) : d157975 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d157975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115511, d157975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115512 q = 1) (hb : d152855 q = 1) : d157976 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d157976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115512, d157976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115513 q = 1) (hb : d152855 q = 1) : d157977 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d157977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115513, d157977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30382 (p : Pattern) (ha : d115519 p = 1) (hb : d152855 p = 1) : d157983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d152855 q = 1) : d157978 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d157978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d157978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30381 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d152855 q = 1) : d157979 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d157979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d157979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d152855 q = 1) : d157980 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d157980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d157980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d152855 q = 1) : d157981 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d157981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d157981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d152855 q = 1) : d157982 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d157982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d157982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d152855 q = 1) : d157983 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d157983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d157983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30383 (p : Pattern) (ha : d115525 p = 1) (hb : d152855 p = 1) : d157989 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d152855 q = 1) : d156872 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d156872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30106 q ha hb
    | true =>
      simp only [d115354, d156872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30150 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d152855 q = 1) : d157110 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d157110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d157110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30199 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d152855 q = 1) : d157111 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d157111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d157111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d152855 q = 1) : d157385 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d157385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d157385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30260 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d152855 q = 1) : d157386 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d157386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d157386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d152855 q = 1) : d157387 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d157387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d157387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d152855 q = 1) : d157702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d157702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d157702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30321 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d152855 q = 1) : d157703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d157703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d157703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d152855 q = 1) : d157704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d157704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d157704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d152855 q = 1) : d157705 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d157705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d157705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d152855 q = 1) : d157984 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d157984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d157984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30382 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d152855 q = 1) : d157985 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d157985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d157985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d152855 q = 1) : d157986 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d157986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d157986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d152855 q = 1) : d157987 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d157987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d157987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d152855 q = 1) : d157988 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d157988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d157988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d152855 q = 1) : d157989 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d157989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d157989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro30384 (p : Pattern) (ha : d115531 p = 1) (hb : d152855 p = 1) : d157995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d152855 q = 1) : d157990 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d157990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30383 q ha hb
    | true =>
      simp only [d115526, d157990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d152855 q = 1) : d157991 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d157991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d157991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d152855 q = 1) : d157992 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d157992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d157992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d152855 q = 1) : d157993 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d157993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d157993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d152855 q = 1) : d157994 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d157994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d157994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d152855 q = 1) : d157995 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d157995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d157995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30385 (p : Pattern) (ha : d115537 p = 1) (hb : d152855 p = 1) : d158001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d152855 q = 1) : d157996 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d157996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30384 q ha hb
    | true =>
      simp only [d115532, d157996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d152855 q = 1) : d157997 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d157997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d157997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d152855 q = 1) : d157998 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d157998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d157998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d152855 q = 1) : d157999 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d157999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d157999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d152855 q = 1) : d158000 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d158000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d158000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d152855 q = 1) : d158001 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d158001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d158001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30386 (p : Pattern) (ha : d115543 p = 1) (hb : d152855 p = 1) : d158007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d152855 q = 1) : d158002 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d158002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30385 q ha hb
    | true =>
      simp only [d115538, d158002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d152855 q = 1) : d158003 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d158003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d158003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d152855 q = 1) : d158004 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d158004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d158004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d152855 q = 1) : d158005 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d158005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d158005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d152855 q = 1) : d158006 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d158006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d158006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d152855 q = 1) : d158007 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d158007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d158007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30387 (p : Pattern) (ha : d115549 p = 1) (hb : d152855 p = 1) : d158013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d152855 q = 1) : d158008 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d158008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30386 q ha hb
    | true =>
      simp only [d115544, d158008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d152855 q = 1) : d158009 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d158009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d158009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d152855 q = 1) : d158010 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d158010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d158010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d152855 q = 1) : d158011 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d158011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d158011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d152855 q = 1) : d158012 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d158012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d158012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d152855 q = 1) : d158013 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d158013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d158013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30388 (p : Pattern) (ha : d115555 p = 1) (hb : d152855 p = 1) : d158019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d152855 q = 1) : d158014 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d158014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30387 q ha hb
    | true =>
      simp only [d115550, d158014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d152855 q = 1) : d158015 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d158015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d158015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d152855 q = 1) : d158016 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d158016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d158016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d152855 q = 1) : d158017 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d158017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d158017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d152855 q = 1) : d158018 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d158018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d158018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d152855 q = 1) : d158019 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d158019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d158019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30389 (p : Pattern) (ha : d115561 p = 1) (hb : d152855 p = 1) : d158025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d152855 q = 1) : d158020 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d158020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30388 q ha hb
    | true =>
      simp only [d115556, d158020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d152855 q = 1) : d158021 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d158021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d158021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d152855 q = 1) : d158022 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d158022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d158022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d152855 q = 1) : d158023 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d158023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d158023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d152855 q = 1) : d158024 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d158024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d158024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d152855 q = 1) : d158025 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d158025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d158025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30390 (p : Pattern) (ha : d115567 p = 1) (hb : d152855 p = 1) : d158031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d152855 q = 1) : d158026 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d158026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30389 q ha hb
    | true =>
      simp only [d115562, d158026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d152855 q = 1) : d158027 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d158027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d158027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d152855 q = 1) : d158028 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d158028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d158028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d152855 q = 1) : d158029 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d158029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d158029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d152855 q = 1) : d158030 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d158030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d158030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d152855 q = 1) : d158031 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d158031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d158031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30391 (p : Pattern) (ha : d154954 p = 1) (hb : d156536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d154954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22 q = 1) (hb : d154953 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d154953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22, d154953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d154954 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d154954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23, d154954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d154954 q = 1) (hb : d156536 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro30392 (p : Pattern) (ha : d154960 p = 1) (hb : d156542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154955 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
    | true =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154956 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154957 q = 1) (hb : d156539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154957, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154957, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154958 q = 1) (hb : d156540 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154958, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154958, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154959 q = 1) (hb : d156541 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154959, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154959, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d154960 q = 1) (hb : d156542 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d154960, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154960, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30393 (p : Pattern) (ha : d154966 p = 1) (hb : d156548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154961 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30392 q ha hb
    | true =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154962 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154963 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154964 q = 1) (hb : d156546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154964, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154964, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154965 q = 1) (hb : d156547 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d154965, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154965, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d154966 q = 1) (hb : d156548 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d154966, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154966, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30394 (p : Pattern) (ha : d154972 p = 1) (hb : d156554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154970 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154971 q = 1) (hb : d156553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154971, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154971, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d154972 q = 1) (hb : d156554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154972, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154972, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30395 (p : Pattern) (ha : d154978 p = 1) (hb : d156560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154974 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154975 q = 1) (hb : d156557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154975, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154975, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154976 q = 1) (hb : d156558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154976, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154976, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154977 q = 1) (hb : d156559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154977, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154977, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154978 q = 1) (hb : d156560 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154978, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154978, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30396 (p : Pattern) (ha : d154979 p = 1) (hb : d156561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154970 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154971 q = 1) (hb : d156553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d154971, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154971, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d154979 q = 1) (hb : d156561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d154979, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154979, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30397 (p : Pattern) (ha : d154985 p = 1) (hb : d156567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154974 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154975 q = 1) (hb : d156557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154975, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154975, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154976 q = 1) (hb : d156558 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154976, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154976, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154977 q = 1) (hb : d156559 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154977, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154977, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d154981 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d154982 q = 1) (hb : d156564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154982, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d154982, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d154983 q = 1) (hb : d156565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154983, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154983, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d154984 q = 1) (hb : d156566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154984, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154984, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d154985 q = 1) (hb : d156567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154985, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154985, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30398 (p : Pattern) (ha : d154990 p = 1) (hb : d156572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154981 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154982 q = 1) (hb : d156564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d154982, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154982, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154983 q = 1) (hb : d156565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d154983, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154983, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154984 q = 1) (hb : d156566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d154984, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154984, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154990 q = 1) (hb : d156572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d154990, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154990, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30399 (p : Pattern) (ha : d155001 p = 1) (hb : d156583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154996 q = 1) (hb : d156578 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154996, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154996, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
  have h2 (q : Pattern) (ha : d154955 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
    | true =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154997 q = 1) (hb : d156579 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154997, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154997, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154956 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154998 q = 1) (hb : d156580 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154998, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154998, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154999 q = 1) (hb : d156581 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154999, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154999, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155000 q = 1) (hb : d156582 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155000, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155000, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155001 q = 1) (hb : d156583 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155001, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155001, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30400 (p : Pattern) (ha : d155007 p = 1) (hb : d156589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155002 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30399 q ha hb
    | true =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155003 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155004 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155005 q = 1) (hb : d156587 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155005, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155005, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155006 q = 1) (hb : d156588 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155006, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155006, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155007 q = 1) (hb : d156589 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155007, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155007, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30401 (p : Pattern) (ha : d155013 p = 1) (hb : d156595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155008 q = 1) (hb : d156590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155008, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30400 q ha hb
    | true =>
      simp only [d155008, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155009 q = 1) (hb : d156591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155009, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155009, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155010 q = 1) (hb : d156592 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155010, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155010, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155011 q = 1) (hb : d156593 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155011, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155011, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155012 q = 1) (hb : d156594 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155012, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155012, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155013 q = 1) (hb : d156595 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155013, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155013, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30402 (p : Pattern) (ha : d155019 p = 1) (hb : d156601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155014 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
    | true =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155015 q = 1) (hb : d156597 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155015, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155015, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155016 q = 1) (hb : d156598 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155016, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155016, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155017 q = 1) (hb : d156599 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155017, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155017, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155018 q = 1) (hb : d156600 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155018, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155018, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155019 q = 1) (hb : d156601 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155019, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155019, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30403 (p : Pattern) (ha : d155025 p = 1) (hb : d156607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154986 q = 1) (hb : d156568 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154986, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30395 q ha hb
    | true =>
      simp only [d154986, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30397 q ha hb
  have h2 (q : Pattern) (ha : d154987 q = 1) (hb : d156569 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154987, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d154987, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d154988 q = 1) (hb : d156570 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154988, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154988, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154989 q = 1) (hb : d156571 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154989, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154989, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154991 q = 1) (hb : d156573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d154991, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154991, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30398 q ha hb
  have h6 (q : Pattern) (ha : d154992 q = 1) (hb : d156574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d154992, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154992, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d154993 q = 1) (hb : d156575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d154993, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d154993, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d154994 q = 1) (hb : d156576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d154994, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d154994, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d154995 q = 1) (hb : d156577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d154995, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154995, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155020 q = 1) (hb : d156602 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155020, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155020, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30402 q ha hb
  have h11 (q : Pattern) (ha : d155021 q = 1) (hb : d156603 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155021, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155021, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155022 q = 1) (hb : d156604 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155022, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155022, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155023 q = 1) (hb : d156605 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155023, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155023, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d155024 q = 1) (hb : d156606 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155024, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155024, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d155025 q = 1) (hb : d156607 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155025, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155025, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30404 (p : Pattern) (ha : d155035 p = 1) (hb : d156617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155031 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155032 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155033 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155034 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155035 q = 1) (hb : d156617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155035, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155035, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30405 (p : Pattern) (ha : d155042 p = 1) (hb : d156624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155031 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155032 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155033 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155034 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155038 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155038, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155038, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155039 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155039, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155039, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155040 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155040, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155040, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155041 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155041, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155041, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155042 q = 1) (hb : d156624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155042, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155042, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30406 (p : Pattern) (ha : d155047 p = 1) (hb : d156629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154970 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155046 q = 1) (hb : d156628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155046, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155046, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155047 q = 1) (hb : d156629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155047, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155047, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30407 (p : Pattern) (ha : d155054 p = 1) (hb : d156636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155052 q = 1) (hb : d156634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155052, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155052, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155053 q = 1) (hb : d156635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155053, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155053, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155054 q = 1) (hb : d156636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155054, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155054, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30408 (p : Pattern) (ha : d155059 p = 1) (hb : d156640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155059 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d21 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25102 q = 1) (hb : d155058 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d155058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25102, d155058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25103 q = 1) (hb : d155059 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d155059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25103, d155059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d155059 q = 1) (hb : d156640 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30409 (p : Pattern) (ha : d155065 p = 1) (hb : d156646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155062 q = 1) (hb : d156643 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155063 q = 1) (hb : d156644 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154955 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
    | true =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d154956 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d154957 q = 1) (hb : d156539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154957, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154957, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d154958 q = 1) (hb : d156540 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154958, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d154958, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155064 q = 1) (hb : d156645 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155064, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155064, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d154959 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155065 q = 1) (hb : d156646 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155065, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155065, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30410 (p : Pattern) (ha : d155071 p = 1) (hb : d156652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155066 q = 1) (hb : d156647 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155066, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30409 q ha hb
    | true =>
      simp only [d155066, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30392 q ha hb
  have h2 (q : Pattern) (ha : d155067 q = 1) (hb : d156648 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155067, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155067, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155068 q = 1) (hb : d156649 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155068, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155068, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d154961 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30392 q ha hb
    | true =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154962 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154963 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155069 q = 1) (hb : d156650 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155069, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155069, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d154964 q = 1) (hb : d156546 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d154964, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d154964, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155070 q = 1) (hb : d156651 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155070, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155070, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155071 q = 1) (hb : d156652 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155071, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155071, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30411 (p : Pattern) (ha : d155077 p = 1) (hb : d156658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155075 q = 1) (hb : d156656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155076 q = 1) (hb : d156657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155076, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155076, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155077 q = 1) (hb : d156658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155077, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155077, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30412 (p : Pattern) (ha : d155083 p = 1) (hb : d156664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155048 q = 1) (hb : d156630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155048, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30406 q ha hb
    | true =>
      simp only [d155048, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155049 q = 1) (hb : d156631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155049, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155049, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155050 q = 1) (hb : d156632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155050, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155050, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155051 q = 1) (hb : d156633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155051, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155051, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155055 q = 1) (hb : d156637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155055, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30407 q ha hb
    | true =>
      simp only [d155055, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155056 q = 1) (hb : d156638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155056, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155056, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155057 q = 1) (hb : d156639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155057, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155057, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d154973 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155079 q = 1) (hb : d156660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155079, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d154974 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155080 q = 1) (hb : d156661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155080, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155081 q = 1) (hb : d156662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155081, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155082 q = 1) (hb : d156663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155082, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155083 q = 1) (hb : d156664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155083, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155083, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30413 (p : Pattern) (ha : d155084 p = 1) (hb : d156665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154970 q = 1) (hb : d156552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d154970, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155046 q = 1) (hb : d156628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155046, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155046, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155084 q = 1) (hb : d156665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155084, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155084, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30414 (p : Pattern) (ha : d155089 p = 1) (hb : d156670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154969 q = 1) (hb : d156551 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d154969, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155052 q = 1) (hb : d156634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155052, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155052, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155053 q = 1) (hb : d156635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155053, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155053, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155089 q = 1) (hb : d156670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155089, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155089, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30415 (p : Pattern) (ha : d155093 p = 1) (hb : d156674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155075 q = 1) (hb : d156656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155076 q = 1) (hb : d156657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155076, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155076, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155093 q = 1) (hb : d156674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155093, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155093, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30416 (p : Pattern) (ha : d155099 p = 1) (hb : d156680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155048 q = 1) (hb : d156630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155048, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30406 q ha hb
    | true =>
      simp only [d155048, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155049 q = 1) (hb : d156631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155049, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155049, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155050 q = 1) (hb : d156632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155050, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155050, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155051 q = 1) (hb : d156633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155051, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155051, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155055 q = 1) (hb : d156637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155055, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30407 q ha hb
    | true =>
      simp only [d155055, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155056 q = 1) (hb : d156638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155056, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155056, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155057 q = 1) (hb : d156639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155057, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155057, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d154973 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155079 q = 1) (hb : d156660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155079, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d154974 q = 1) (hb : d156556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d154974, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155080 q = 1) (hb : d156661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155080, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155081 q = 1) (hb : d156662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155081, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155082 q = 1) (hb : d156663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155082, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155085 q = 1) (hb : d156666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155085, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30413 q ha hb
    | true =>
      simp only [d155085, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d155086 q = 1) (hb : d156667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155086, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155086, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155087 q = 1) (hb : d156668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155087, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155087, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d155088 q = 1) (hb : d156669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155088, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155088, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155090 q = 1) (hb : d156671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155090, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30414 q ha hb
    | true =>
      simp only [d155090, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d155091 q = 1) (hb : d156672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155091, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155091, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d155092 q = 1) (hb : d156673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155092, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155092, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155094 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
    | true =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d154980 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d155095 q = 1) (hb : d156676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d155095, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d154981 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d155096 q = 1) (hb : d156677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d155096, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d155097 q = 1) (hb : d156678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155097, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d155097, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d155098 q = 1) (hb : d156679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155098, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155098, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d155099 q = 1) (hb : d156680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155099, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155099, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30417 (p : Pattern) (ha : d155101 p = 1) (hb : d156682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155031 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155032 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155033 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155034 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155101 q = 1) (hb : d156682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155101, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155101, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30418 (p : Pattern) (ha : d155108 p = 1) (hb : d156689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155094 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
    | true =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155095 q = 1) (hb : d156676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155095, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d154981 q = 1) (hb : d156563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154981, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155096 q = 1) (hb : d156677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155096, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155106 q = 1) (hb : d156687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155106, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155106, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155107 q = 1) (hb : d156688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155107, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155107, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155108 q = 1) (hb : d156689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155108, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155108, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30419 (p : Pattern) (ha : d155119 p = 1) (hb : d156700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155114 q = 1) (hb : d156695 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
  have h2 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155115 q = 1) (hb : d156696 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155116 q = 1) (hb : d156697 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155117 q = 1) (hb : d156698 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d154996 q = 1) (hb : d156578 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154996, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154996, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
  have h8 (q : Pattern) (ha : d154955 q = 1) (hb : d156537 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30391 q ha hb
    | true =>
      simp only [d154955, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d154997 q = 1) (hb : d156579 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154997, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d154997, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d154956 q = 1) (hb : d156538 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d154956, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d154998 q = 1) (hb : d156580 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154998, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d154998, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d154999 q = 1) (hb : d156581 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154999, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d154999, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155118 q = 1) (hb : d156699 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155118, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155118, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155119 q = 1) (hb : d156700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155119, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155119, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30420 (p : Pattern) (ha : d155125 p = 1) (hb : d156706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155120 q = 1) (hb : d156701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155120, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30419 q ha hb
    | true =>
      simp only [d155120, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30399 q ha hb
  have h2 (q : Pattern) (ha : d155121 q = 1) (hb : d156702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155121, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155121, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155122 q = 1) (hb : d156703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155122, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155122, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155002 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30399 q ha hb
    | true =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155003 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155004 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155123 q = 1) (hb : d156704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155123, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155123, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155005 q = 1) (hb : d156587 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155005, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155005, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155124 q = 1) (hb : d156705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155124, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155124, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155125 q = 1) (hb : d156706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155125, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155125, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30421 (p : Pattern) (ha : d155131 p = 1) (hb : d156712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155126 q = 1) (hb : d156707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30420 q ha hb
    | true =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155127 q = 1) (hb : d156708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155008 q = 1) (hb : d156590 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155008, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30400 q ha hb
    | true =>
      simp only [d155008, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155009 q = 1) (hb : d156591 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155009, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155009, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155128 q = 1) (hb : d156709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155128, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155128, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155129 q = 1) (hb : d156710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155129, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155129, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155130 q = 1) (hb : d156711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155130, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155130, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155131 q = 1) (hb : d156712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155131, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155131, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30422 (p : Pattern) (ha : d155137 p = 1) (hb : d156718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155132 q = 1) (hb : d156713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155132, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30421 q ha hb
    | true =>
      simp only [d155132, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155133 q = 1) (hb : d156714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155133, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155133, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155014 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
    | true =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155015 q = 1) (hb : d156597 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155015, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155015, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155134 q = 1) (hb : d156715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155134, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155134, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155135 q = 1) (hb : d156716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155135, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155135, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155136 q = 1) (hb : d156717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155136, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155136, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155137 q = 1) (hb : d156718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155137, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155137, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30423 (p : Pattern) (ha : d155143 p = 1) (hb : d156724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155036 q = 1) (hb : d156618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155036, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155036, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30404 q ha hb
  have h2 (q : Pattern) (ha : d155037 q = 1) (hb : d156619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155037, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155037, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155043 q = 1) (hb : d156625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155043, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30404 q ha hb
    | true =>
      simp only [d155043, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30405 q ha hb
  have h4 (q : Pattern) (ha : d155044 q = 1) (hb : d156626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155044, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155044, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155045 q = 1) (hb : d156627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155045, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155045, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155100 q = 1) (hb : d156681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155100, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30412 q ha hb
    | true =>
      simp only [d155100, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30416 q ha hb
  have h7 (q : Pattern) (ha : d155102 q = 1) (hb : d156683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155102, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30417 q ha hb
    | true =>
      simp only [d155102, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155103 q = 1) (hb : d156684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155103, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155103, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155104 q = 1) (hb : d156685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155104, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155104, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155105 q = 1) (hb : d156686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155105, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155105, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155109 q = 1) (hb : d156690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155109, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155109, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30418 q ha hb
  have h12 (q : Pattern) (ha : d155110 q = 1) (hb : d156691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155110, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155110, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155111 q = 1) (hb : d156692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155111, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155111, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d155112 q = 1) (hb : d156693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155112, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155112, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d155113 q = 1) (hb : d156694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155113, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155113, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155138 q = 1) (hb : d156719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155138, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155138, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30422 q ha hb
  have h17 (q : Pattern) (ha : d155139 q = 1) (hb : d156720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155139, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155139, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d155140 q = 1) (hb : d156721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155140, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155140, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d155141 q = 1) (hb : d156722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155141, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d155141, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d155142 q = 1) (hb : d156723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155142, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155142, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d155143 q = 1) (hb : d156724 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155143, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155143, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro30424 (p : Pattern) (ha : d155149 p = 1) (hb : d156730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155026 q = 1) (hb : d156608 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155026, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155026, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30403 q ha hb
  have h2 (q : Pattern) (ha : d155027 q = 1) (hb : d156609 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155027, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155027, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155028 q = 1) (hb : d156610 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155028, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155028, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155029 q = 1) (hb : d156611 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155029, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155029, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155030 q = 1) (hb : d156612 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155030, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155030, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155144 q = 1) (hb : d156725 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155144, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155144, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30423 q ha hb
  have h7 (q : Pattern) (ha : d155145 q = 1) (hb : d156726 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155145, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155145, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155146 q = 1) (hb : d156727 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155146, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155146, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155147 q = 1) (hb : d156728 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155147, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155147, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155148 q = 1) (hb : d156729 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155148, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155148, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155149 q = 1) (hb : d156730 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155149, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155149, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30425 (p : Pattern) (ha : d155154 p = 1) (hb : d156735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h2 (q : Pattern) (ha : d155150 q = 1) (hb : d156731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155151 q = 1) (hb : d156732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155152 q = 1) (hb : d156733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155153 q = 1) (hb : d156734 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155154 q = 1) (hb : d156735 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155154, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155154, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30426 (p : Pattern) (ha : d155161 p = 1) (hb : d156742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h2 (q : Pattern) (ha : d155150 q = 1) (hb : d156731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155151 q = 1) (hb : d156732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155152 q = 1) (hb : d156733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155153 q = 1) (hb : d156734 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155094 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
    | true =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
  have h7 (q : Pattern) (ha : d155157 q = 1) (hb : d156738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155157, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155157, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155158 q = 1) (hb : d156739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155158, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155158, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155159 q = 1) (hb : d156740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155159, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155159, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155160 q = 1) (hb : d156741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155160, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155160, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155161 q = 1) (hb : d156742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155161, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155161, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30427 (p : Pattern) (ha : d155166 p = 1) (hb : d156747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155075 q = 1) (hb : d156656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155165 q = 1) (hb : d156746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155165, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155165, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155166 q = 1) (hb : d156747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155166, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155166, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30428 (p : Pattern) (ha : d155173 p = 1) (hb : d156754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155171 q = 1) (hb : d156752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155171, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155171, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155172 q = 1) (hb : d156753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155172, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155172, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155173 q = 1) (hb : d156754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155173, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155173, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30429 (p : Pattern) (ha : d155178 p = 1) (hb : d156758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25210 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9796 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25211 q = 1) (hb : d155177 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d155177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25211, d155177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25212 q = 1) (hb : d155178 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d155178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25212, d155178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d155178 q = 1) (hb : d156758 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30430 (p : Pattern) (ha : d155191 p = 1) (hb : d156764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155179 q = 1) (hb : d156759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
    | true =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155180 q = 1) (hb : d156760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155181 q = 1) (hb : d156761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155181, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155181, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155182 q = 1) (hb : d156762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155182, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155182, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155062 q = 1) (hb : d156643 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155063 q = 1) (hb : d156644 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155183 q = 1) (hb : d156763 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155183, d156763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155183, d156763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155190 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155191 q = 1) (hb : d156764 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155191, d156764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155191, d156764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30431 (p : Pattern) (ha : d155197 p = 1) (hb : d156770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155192 q = 1) (hb : d156765 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155192, d156765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30430 q ha hb
    | true =>
      simp only [d155192, d156765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30409 q ha hb
  have h2 (q : Pattern) (ha : d155193 q = 1) (hb : d156766 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155193, d156766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155193, d156766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155194 q = 1) (hb : d156767 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155194, d156767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155194, d156767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155066 q = 1) (hb : d156647 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155066, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30409 q ha hb
    | true =>
      simp only [d155066, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30392 q ha hb
  have h5 (q : Pattern) (ha : d155067 q = 1) (hb : d156648 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155067, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155067, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155068 q = 1) (hb : d156649 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155068, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155068, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155195 q = 1) (hb : d156768 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155195, d156768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155195, d156768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d154961 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30392 q ha hb
    | true =>
      simp only [d154961, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d154962 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154962, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d154963 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154963, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155069 q = 1) (hb : d156650 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155069, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155069, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155196 q = 1) (hb : d156769 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155196, d156769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155196, d156769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155197 q = 1) (hb : d156770 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155197, d156770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155197, d156770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30432 (p : Pattern) (ha : d155203 p = 1) (hb : d156776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155198 q = 1) (hb : d156771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155198, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30431 q ha hb
    | true =>
      simp only [d155198, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155199 q = 1) (hb : d156772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155199, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155199, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155200 q = 1) (hb : d156773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155200, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155200, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155201 q = 1) (hb : d156774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155201, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155201, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155202 q = 1) (hb : d156775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155202, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155202, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155203 q = 1) (hb : d156776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155203, d156776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155203, d156776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30433 (p : Pattern) (ha : d155209 p = 1) (hb : d156782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155206 q = 1) (hb : d156779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155206, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155206, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155207 q = 1) (hb : d156780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155207, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155207, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155208 q = 1) (hb : d156781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155208, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155208, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155209 q = 1) (hb : d156782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155209, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155209, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30434 (p : Pattern) (ha : d155215 p = 1) (hb : d156788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155167 q = 1) (hb : d156748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155167, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30427 q ha hb
    | true =>
      simp only [d155167, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30406 q ha hb
  have h2 (q : Pattern) (ha : d155168 q = 1) (hb : d156749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155168, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155168, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155169 q = 1) (hb : d156750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155169, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155169, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155170 q = 1) (hb : d156751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155170, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155170, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155174 q = 1) (hb : d156755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155174, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30428 q ha hb
    | true =>
      simp only [d155174, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30407 q ha hb
  have h6 (q : Pattern) (ha : d155175 q = 1) (hb : d156756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155175, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155175, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155176 q = 1) (hb : d156757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155176, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155176, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155204 q = 1) (hb : d156777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155204, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30432 q ha hb
    | true =>
      simp only [d155204, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155205 q = 1) (hb : d156778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155205, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155205, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155210 q = 1) (hb : d156783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155210, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30433 q ha hb
    | true =>
      simp only [d155210, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155211 q = 1) (hb : d156784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155211, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155211, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155212 q = 1) (hb : d156785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155212, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155212, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155213 q = 1) (hb : d156786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155213, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155213, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155214 q = 1) (hb : d156787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155214, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155214, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155215 q = 1) (hb : d156788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155215, d156788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155215, d156788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30435 (p : Pattern) (ha : d155216 p = 1) (hb : d156789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155075 q = 1) (hb : d156656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155075, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155165 q = 1) (hb : d156746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155165, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155165, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155216 q = 1) (hb : d156789 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155216, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155216, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30436 (p : Pattern) (ha : d155221 p = 1) (hb : d156794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d154967 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30393 q ha hb
    | true =>
      simp only [d154967, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d154968 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d154968, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155074 q = 1) (hb : d156655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155074, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155171 q = 1) (hb : d156752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155171, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155171, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155172 q = 1) (hb : d156753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155172, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155172, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155221 q = 1) (hb : d156794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155221, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155221, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30437 (p : Pattern) (ha : d155225 p = 1) (hb : d156798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155198 q = 1) (hb : d156771 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155198, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30431 q ha hb
    | true =>
      simp only [d155198, d156771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155199 q = 1) (hb : d156772 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155199, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155199, d156772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155200 q = 1) (hb : d156773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155200, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155200, d156773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155201 q = 1) (hb : d156774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155201, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155201, d156774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155202 q = 1) (hb : d156775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155202, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155202, d156775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155225 q = 1) (hb : d156798 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155225, d156798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155225, d156798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30438 (p : Pattern) (ha : d155228 p = 1) (hb : d156801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155072 q = 1) (hb : d156653 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30410 q ha hb
    | true =>
      simp only [d155072, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155073 q = 1) (hb : d156654 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155073, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155206 q = 1) (hb : d156779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155206, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155206, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155207 q = 1) (hb : d156780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155207, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155207, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155208 q = 1) (hb : d156781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155208, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155208, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155228 q = 1) (hb : d156801 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155228, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155228, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30439 (p : Pattern) (ha : d155234 p = 1) (hb : d156807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155167 q = 1) (hb : d156748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155167, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30427 q ha hb
    | true =>
      simp only [d155167, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30406 q ha hb
  have h2 (q : Pattern) (ha : d155168 q = 1) (hb : d156749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155168, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155168, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155169 q = 1) (hb : d156750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155169, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155169, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155170 q = 1) (hb : d156751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155170, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155170, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155174 q = 1) (hb : d156755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155174, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30428 q ha hb
    | true =>
      simp only [d155174, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30407 q ha hb
  have h6 (q : Pattern) (ha : d155175 q = 1) (hb : d156756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155175, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155175, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155176 q = 1) (hb : d156757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155176, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155176, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155204 q = 1) (hb : d156777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155204, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30432 q ha hb
    | true =>
      simp only [d155204, d156777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155205 q = 1) (hb : d156778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155205, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155205, d156778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155210 q = 1) (hb : d156783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155210, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30433 q ha hb
    | true =>
      simp only [d155210, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155211 q = 1) (hb : d156784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155211, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155211, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155212 q = 1) (hb : d156785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155212, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155212, d156785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155213 q = 1) (hb : d156786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155213, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155213, d156786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155214 q = 1) (hb : d156787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155214, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155214, d156787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155217 q = 1) (hb : d156790 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155217, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30435 q ha hb
    | true =>
      simp only [d155217, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30413 q ha hb
  have h17 (q : Pattern) (ha : d155218 q = 1) (hb : d156791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155218, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155218, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155219 q = 1) (hb : d156792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155219, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155219, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d155220 q = 1) (hb : d156793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155220, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155220, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155222 q = 1) (hb : d156795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155222, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30436 q ha hb
    | true =>
      simp only [d155222, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30414 q ha hb
  have h21 (q : Pattern) (ha : d155223 q = 1) (hb : d156796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155223, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155223, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d155224 q = 1) (hb : d156797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155224, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155224, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155226 q = 1) (hb : d156799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155226, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30437 q ha hb
    | true =>
      simp only [d155226, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d155227 q = 1) (hb : d156800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155227, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d155227, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d155229 q = 1) (hb : d156802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155229, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30438 q ha hb
    | true =>
      simp only [d155229, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d155230 q = 1) (hb : d156803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155230, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d155230, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d155231 q = 1) (hb : d156804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155231, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d155231, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d155232 q = 1) (hb : d156805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155232, d156805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d155232, d156805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d155233 q = 1) (hb : d156806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155233, d156806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155233, d156806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d155234 q = 1) (hb : d156807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155234, d156807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155234, d156807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30440 (p : Pattern) (ha : d155236 p = 1) (hb : d156809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h2 (q : Pattern) (ha : d155150 q = 1) (hb : d156731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155150, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155151 q = 1) (hb : d156732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155151, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155152 q = 1) (hb : d156733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155152, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155153 q = 1) (hb : d156734 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155153, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155031 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155031, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155032 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155032, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155033 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155033, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155034 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155034, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155236 q = 1) (hb : d156809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155236, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155236, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30441 (p : Pattern) (ha : d155243 p = 1) (hb : d156816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155226 q = 1) (hb : d156799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155226, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30437 q ha hb
    | true =>
      simp only [d155226, d156799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155227 q = 1) (hb : d156800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155227, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155227, d156800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155229 q = 1) (hb : d156802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155229, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30438 q ha hb
    | true =>
      simp only [d155229, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155230 q = 1) (hb : d156803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155230, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155230, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155231 q = 1) (hb : d156804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155231, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155231, d156804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155241 q = 1) (hb : d156814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155241, d156814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155241, d156814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155242 q = 1) (hb : d156815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155242, d156815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155242, d156815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155243 q = 1) (hb : d156816 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155243, d156816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155243, d156816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30442 (p : Pattern) (ha : d155245 p = 1) (hb : d156818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155038 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155038, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155038, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155039 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155039, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155039, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155040 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155040, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155040, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155041 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155041, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155041, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155245 q = 1) (hb : d156818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155245, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155245, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30443 (p : Pattern) (ha : d155261 p = 1) (hb : d156829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155251 q = 1) (hb : d156824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155251, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155251, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
  have h2 (q : Pattern) (ha : d155179 q = 1) (hb : d156759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
    | true =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155252 q = 1) (hb : d156825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155252, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155252, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155180 q = 1) (hb : d156760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155253 q = 1) (hb : d156826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155253, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155253, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155254 q = 1) (hb : d156827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155254, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155254, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155114 q = 1) (hb : d156695 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
  have h8 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155115 q = 1) (hb : d156696 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d155116 q = 1) (hb : d156697 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155117 q = 1) (hb : d156698 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155255 q = 1) (hb : d156828 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155255, d156828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155255, d156828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155261 q = 1) (hb : d156829 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155261, d156829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155261, d156829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30444 (p : Pattern) (ha : d155267 p = 1) (hb : d156835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155262 q = 1) (hb : d156830 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155262, d156830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30443 q ha hb
    | true =>
      simp only [d155262, d156830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30419 q ha hb
  have h2 (q : Pattern) (ha : d155263 q = 1) (hb : d156831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155263, d156831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155263, d156831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155264 q = 1) (hb : d156832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155264, d156832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155264, d156832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155120 q = 1) (hb : d156701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155120, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30419 q ha hb
    | true =>
      simp only [d155120, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30399 q ha hb
  have h5 (q : Pattern) (ha : d155121 q = 1) (hb : d156702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155121, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155121, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155122 q = 1) (hb : d156703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155122, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155122, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155265 q = 1) (hb : d156833 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155265, d156833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155265, d156833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155002 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30399 q ha hb
    | true =>
      simp only [d155002, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155003 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155003, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155004 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155004, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155123 q = 1) (hb : d156704 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155123, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155123, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155266 q = 1) (hb : d156834 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155266, d156834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155266, d156834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155267 q = 1) (hb : d156835 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155267, d156835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155267, d156835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30445 (p : Pattern) (ha : d155273 p = 1) (hb : d156841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155268 q = 1) (hb : d156836 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155268, d156836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30444 q ha hb
    | true =>
      simp only [d155268, d156836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155269 q = 1) (hb : d156837 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155269, d156837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155269, d156837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155126 q = 1) (hb : d156707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30420 q ha hb
    | true =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155127 q = 1) (hb : d156708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155270 q = 1) (hb : d156838 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155270, d156838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155270, d156838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155271 q = 1) (hb : d156839 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155271, d156839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155271, d156839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155272 q = 1) (hb : d156840 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155272, d156840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155272, d156840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155273 q = 1) (hb : d156841 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155273, d156841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155273, d156841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30446 (p : Pattern) (ha : d155279 p = 1) (hb : d156847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155126 q = 1) (hb : d156707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30420 q ha hb
    | true =>
      simp only [d155126, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155127 q = 1) (hb : d156708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155127, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155276 q = 1) (hb : d156844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155276, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155276, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155277 q = 1) (hb : d156845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155277, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155277, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155278 q = 1) (hb : d156846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155278, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155278, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155279 q = 1) (hb : d156847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155279, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155279, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30447 (p : Pattern) (ha : d155285 p = 1) (hb : d156853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155274 q = 1) (hb : d156842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155274, d156842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30445 q ha hb
    | true =>
      simp only [d155274, d156842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30421 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155132 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155275 q = 1) (hb : d156843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155275, d156843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155275, d156843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155280 q = 1) (hb : d156848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155280, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30446 q ha hb
    | true =>
      simp only [d155280, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155281 q = 1) (hb : d156849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155281, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155281, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155282 q = 1) (hb : d156850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155282, d156850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155282, d156850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155283 q = 1) (hb : d156851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155283, d156851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155283, d156851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155284 q = 1) (hb : d156852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155284, d156852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155284, d156852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155285 q = 1) (hb : d156853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155285, d156853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155285, d156853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30448 (p : Pattern) (ha : d155291 p = 1) (hb : d156859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155014 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
    | true =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155287 q = 1) (hb : d156855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155287, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155287, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155288 q = 1) (hb : d156856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155288, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155288, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155289 q = 1) (hb : d156857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155289, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155289, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155290 q = 1) (hb : d156858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155290, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155290, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155291 q = 1) (hb : d156859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155291, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155291, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30449 (p : Pattern) (ha : d155297 p = 1) (hb : d156865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155155 q = 1) (hb : d156736 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155155, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155155, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30425 q ha hb
  have h2 (q : Pattern) (ha : d155156 q = 1) (hb : d156737 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155156, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155156, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155162 q = 1) (hb : d156743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155162, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30425 q ha hb
    | true =>
      simp only [d155162, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30426 q ha hb
  have h4 (q : Pattern) (ha : d155163 q = 1) (hb : d156744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155163, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155163, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155164 q = 1) (hb : d156745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155164, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155164, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155235 q = 1) (hb : d156808 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155235, d156808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30434 q ha hb
    | true =>
      simp only [d155235, d156808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30439 q ha hb
  have h7 (q : Pattern) (ha : d155237 q = 1) (hb : d156810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155237, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30440 q ha hb
    | true =>
      simp only [d155237, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30405 q ha hb
  have h8 (q : Pattern) (ha : d155238 q = 1) (hb : d156811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155238, d156811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155238, d156811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155239 q = 1) (hb : d156812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155239, d156812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155239, d156812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155240 q = 1) (hb : d156813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155240, d156813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155240, d156813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155244 q = 1) (hb : d156817 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155244, d156817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155244, d156817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30441 q ha hb
  have h12 (q : Pattern) (ha : d155246 q = 1) (hb : d156819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155246, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155246, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30442 q ha hb
  have h13 (q : Pattern) (ha : d155247 q = 1) (hb : d156820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155247, d156820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155247, d156820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155248 q = 1) (hb : d156821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155248, d156821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155248, d156821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d155249 q = 1) (hb : d156822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155249, d156822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155249, d156822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d155250 q = 1) (hb : d156823 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155250, d156823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155250, d156823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155286 q = 1) (hb : d156854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155286, d156854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155286, d156854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30447 q ha hb
  have h18 (q : Pattern) (ha : d155292 q = 1) (hb : d156860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155292, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155292, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30448 q ha hb
  have h19 (q : Pattern) (ha : d155293 q = 1) (hb : d156861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155293, d156861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155293, d156861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155294 q = 1) (hb : d156862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155294, d156862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155294, d156862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d155295 q = 1) (hb : d156863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155295, d156863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d155295, d156863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d155296 q = 1) (hb : d156864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155296, d156864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155296, d156864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155297 q = 1) (hb : d156865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155297, d156865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155297, d156865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30450 (p : Pattern) (ha : d155303 p = 1) (hb : d156871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155298 q = 1) (hb : d156866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155298, d156866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155298, d156866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30449 q ha hb
  have h2 (q : Pattern) (ha : d155299 q = 1) (hb : d156867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155299, d156867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155299, d156867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155300 q = 1) (hb : d156868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155300, d156868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155300, d156868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155301 q = 1) (hb : d156869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155301, d156869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155301, d156869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155302 q = 1) (hb : d156870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155302, d156870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155302, d156870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155303 q = 1) (hb : d156871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155303, d156871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155303, d156871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30451 (p : Pattern) (ha : d155065 p = 1) (hb : d156874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155062 q = 1) (hb : d156643 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155062, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155063 q = 1) (hb : d156644 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155063, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d154958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155064 q = 1) (hb : d156873 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155064, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155064, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d154959 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155065 q = 1) (hb : d156874 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155065, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155065, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro30452 (p : Pattern) (ha : d155307 p = 1) (hb : d156884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155192 q = 1) (hb : d156875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155192, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30430 q ha hb
    | true =>
      simp only [d155192, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30451 q ha hb
  have h2 (q : Pattern) (ha : d155193 q = 1) (hb : d156876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155193, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155193, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155194 q = 1) (hb : d156877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155194, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155194, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154960 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155066 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30451 q ha hb
    | true =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155067 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155068 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155195 q = 1) (hb : d156881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155195, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155195, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155305 q = 1) (hb : d156882 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155305, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155305, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155306 q = 1) (hb : d156883 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155306, d156883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155306, d156883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155307 q = 1) (hb : d156884 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155307, d156884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155307, d156884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro30453 (p : Pattern) (ha : d155311 p = 1) (hb : d156888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155066 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30451 q ha hb
    | true =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d155067 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155068 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155305 q = 1) (hb : d156882 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155305, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155305, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155310 q = 1) (hb : d156887 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155310, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155310, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155311 q = 1) (hb : d156888 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155311, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155311, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro30454 (p : Pattern) (ha : d155317 p = 1) (hb : d156894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155315 q = 1) (hb : d156892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155316 q = 1) (hb : d156893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155316, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155316, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155317 q = 1) (hb : d156894 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155317, d156894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155317, d156894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30455 (p : Pattern) (ha : d155321 p = 1) (hb : d156898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155319 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155320 q = 1) (hb : d156897 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155320, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155320, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155321 q = 1) (hb : d156898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155321, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155321, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30456 (p : Pattern) (ha : d155327 p = 1) (hb : d156904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155322 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
    | true =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
  have h2 (q : Pattern) (ha : d155323 q = 1) (hb : d156900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155324 q = 1) (hb : d156901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155325 q = 1) (hb : d156902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155326 q = 1) (hb : d156903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155327 q = 1) (hb : d156904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155327, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155327, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30457 (p : Pattern) (ha : d155330 p = 1) (hb : d156907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155315 q = 1) (hb : d156892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155316 q = 1) (hb : d156893 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155316, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155316, d156893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155330 q = 1) (hb : d156907 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155330, d156907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155330, d156907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30458 (p : Pattern) (ha : d155331 p = 1) (hb : d156908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155319 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155320 q = 1) (hb : d156897 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155320, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155320, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155331 q = 1) (hb : d156908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155331, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155331, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30459 (p : Pattern) (ha : d155337 p = 1) (hb : d156914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155322 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
    | true =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
  have h2 (q : Pattern) (ha : d155323 q = 1) (hb : d156900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155324 q = 1) (hb : d156901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155325 q = 1) (hb : d156902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155326 q = 1) (hb : d156903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155332 q = 1) (hb : d156909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30457 q ha hb
    | true =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30458 q ha hb
  have h7 (q : Pattern) (ha : d155333 q = 1) (hb : d156910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155333, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155333, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155334 q = 1) (hb : d156911 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155334, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155334, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155335 q = 1) (hb : d156912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155335, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155335, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155336 q = 1) (hb : d156913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155336, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155336, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155337 q = 1) (hb : d156914 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155337, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155337, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30460 (p : Pattern) (ha : d155342 p = 1) (hb : d156919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155315 q = 1) (hb : d156892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155341 q = 1) (hb : d156918 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155341, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155341, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155342 q = 1) (hb : d156919 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155342, d156919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155342, d156919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30461 (p : Pattern) (ha : d155344 p = 1) (hb : d156921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155319 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155343 q = 1) (hb : d156920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155343, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155343, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155344 q = 1) (hb : d156921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155344, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155344, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30462 (p : Pattern) (ha : d155351 p = 1) (hb : d156928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155349 q = 1) (hb : d156926 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155349, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155349, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155350 q = 1) (hb : d156927 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155350, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155350, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155351 q = 1) (hb : d156928 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155351, d156928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155351, d156928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30463 (p : Pattern) (ha : d155354 p = 1) (hb : d156931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155352 q = 1) (hb : d156929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155352, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155352, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155353 q = 1) (hb : d156930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155353, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155353, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155354 q = 1) (hb : d156931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155354, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155354, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30464 (p : Pattern) (ha : d155359 p = 1) (hb : d156935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d531 q = 1) (hb : d52278 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25428 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d52284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75 q ha hb
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d25429 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25430 q = 1) (hb : d155358 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d155358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25430, d155358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25431 q = 1) (hb : d155359 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d155359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25431, d155359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d155359 q = 1) (hb : d156935 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30465 (p : Pattern) (ha : d155372 p = 1) (hb : d156941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155360 q = 1) (hb : d156936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155360, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30464 q ha hb
    | true =>
      simp only [d155360, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155361 q = 1) (hb : d156937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155361, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155361, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155362 q = 1) (hb : d156938 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155362, d156938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155362, d156938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155363 q = 1) (hb : d156939 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155363, d156939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155363, d156939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155179 q = 1) (hb : d156759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
    | true =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155180 q = 1) (hb : d156760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155181 q = 1) (hb : d156761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155181, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155181, d156761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155182 q = 1) (hb : d156762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155182, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155182, d156762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155364 q = 1) (hb : d156940 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155364, d156940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155364, d156940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155371 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155372 q = 1) (hb : d156941 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155372, d156941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155372, d156941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30466 (p : Pattern) (ha : d155185 p = 1) (hb : d156947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155185 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37008 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d37008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155184 q = 1) (hb : d156945 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d155184, d156945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d155184, d156945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d155185 q = 1) (hb : d156946 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d155185, d156946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155185, d156946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d155185 q = 1) (hb : d156947 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30467 (p : Pattern) (ha : d155376 p = 1) (hb : d156953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155186 q = 1) (hb : d156948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155186, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30466 q ha hb
    | true =>
      simp only [d155186, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155187 q = 1) (hb : d156949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155187, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155187, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155188 q = 1) (hb : d156950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155188, d156950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155188, d156950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155189 q = 1) (hb : d156951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155189, d156951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155189, d156951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d154958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155190 q = 1) (hb : d156952 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155190, d156952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155190, d156952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d154959 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155376 q = 1) (hb : d156953 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155376, d156953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155376, d156953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro30468 (p : Pattern) (ha : d155382 p = 1) (hb : d156959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155373 q = 1) (hb : d156942 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155373, d156942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30465 q ha hb
    | true =>
      simp only [d155373, d156942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30430 q ha hb
  have h2 (q : Pattern) (ha : d155374 q = 1) (hb : d156943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155374, d156943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155374, d156943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155375 q = 1) (hb : d156944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155375, d156944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155375, d156944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155377 q = 1) (hb : d156954 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155377, d156954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30430 q ha hb
    | true =>
      simp only [d155377, d156954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30467 q ha hb
  have h5 (q : Pattern) (ha : d155378 q = 1) (hb : d156955 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155378, d156955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155378, d156955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155379 q = 1) (hb : d156956 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155379, d156956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155379, d156956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155380 q = 1) (hb : d156957 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155380, d156957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155380, d156957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155192 q = 1) (hb : d156875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155192, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30430 q ha hb
    | true =>
      simp only [d155192, d156875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30451 q ha hb
  have h9 (q : Pattern) (ha : d155193 q = 1) (hb : d156876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155193, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155193, d156876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155194 q = 1) (hb : d156877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155194, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155194, d156877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d154960 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155066 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30451 q ha hb
    | true =>
      simp only [d155066, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d155067 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155067, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155068 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155068, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155195 q = 1) (hb : d156881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155195, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155195, d156881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155381 q = 1) (hb : d156958 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155381, d156958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155381, d156958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155382 q = 1) (hb : d156959 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155382, d156959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155382, d156959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro30469 (p : Pattern) (ha : d155388 p = 1) (hb : d156965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155383 q = 1) (hb : d156960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155383, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30468 q ha hb
    | true =>
      simp only [d155383, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155384 q = 1) (hb : d156961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155384, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155384, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155385 q = 1) (hb : d156962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155385, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155385, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155386 q = 1) (hb : d156963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155386, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155386, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155387 q = 1) (hb : d156964 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155387, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155387, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155388 q = 1) (hb : d156965 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155388, d156965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155388, d156965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30470 (p : Pattern) (ha : d155394 p = 1) (hb : d156971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155391 q = 1) (hb : d156968 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155391, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155391, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155392 q = 1) (hb : d156969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155392, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155392, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155393 q = 1) (hb : d156970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155393, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155393, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155394 q = 1) (hb : d156971 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155394, d156971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155394, d156971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30471 (p : Pattern) (ha : d155400 p = 1) (hb : d156977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155345 q = 1) (hb : d156922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155345, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30460 q ha hb
    | true =>
      simp only [d155345, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30461 q ha hb
  have h2 (q : Pattern) (ha : d155346 q = 1) (hb : d156923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155346, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155346, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155347 q = 1) (hb : d156924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155347, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155347, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155348 q = 1) (hb : d156925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155348, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155348, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155355 q = 1) (hb : d156932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155355, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30462 q ha hb
    | true =>
      simp only [d155355, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30463 q ha hb
  have h6 (q : Pattern) (ha : d155356 q = 1) (hb : d156933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155356, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155356, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155357 q = 1) (hb : d156934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155357, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155357, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155389 q = 1) (hb : d156966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155389, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30469 q ha hb
    | true =>
      simp only [d155389, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155390 q = 1) (hb : d156967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155390, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155390, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155395 q = 1) (hb : d156972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155395, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30470 q ha hb
    | true =>
      simp only [d155395, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155396 q = 1) (hb : d156973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155396, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155396, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155397 q = 1) (hb : d156974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155397, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155397, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155398 q = 1) (hb : d156975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155398, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155398, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155399 q = 1) (hb : d156976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155399, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155399, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155400 q = 1) (hb : d156977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155400, d156977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155400, d156977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30472 (p : Pattern) (ha : d155401 p = 1) (hb : d156978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155315 q = 1) (hb : d156892 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155315, d156892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155341 q = 1) (hb : d156918 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155341, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155341, d156918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155401 q = 1) (hb : d156978 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155401, d156978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155401, d156978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30473 (p : Pattern) (ha : d155402 p = 1) (hb : d156979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155319 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155319, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155343 q = 1) (hb : d156920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155343, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155343, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155402 q = 1) (hb : d156979 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155402, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155402, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30474 (p : Pattern) (ha : d155407 p = 1) (hb : d156984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155314 q = 1) (hb : d156891 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155314, d156891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155349 q = 1) (hb : d156926 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155349, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155349, d156926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155350 q = 1) (hb : d156927 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155350, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155350, d156927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155407 q = 1) (hb : d156984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155407, d156984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155407, d156984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30475 (p : Pattern) (ha : d155408 p = 1) (hb : d156985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155312 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30453 q ha hb
    | true =>
      simp only [d155312, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155313 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155313, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155318 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155318, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155352 q = 1) (hb : d156929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155352, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155352, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155353 q = 1) (hb : d156930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155353, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155353, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155408 q = 1) (hb : d156985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155408, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155408, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30476 (p : Pattern) (ha : d155412 p = 1) (hb : d156989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155383 q = 1) (hb : d156960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155383, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30468 q ha hb
    | true =>
      simp only [d155383, d156960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155384 q = 1) (hb : d156961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155384, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155384, d156961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155385 q = 1) (hb : d156962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155385, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155385, d156962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155386 q = 1) (hb : d156963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155386, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155386, d156963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155387 q = 1) (hb : d156964 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155387, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155387, d156964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155412 q = 1) (hb : d156989 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155412, d156989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155412, d156989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30477 (p : Pattern) (ha : d155415 p = 1) (hb : d156992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155308 q = 1) (hb : d156885 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30452 q ha hb
    | true =>
      simp only [d155308, d156885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155309 q = 1) (hb : d156886 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155309, d156886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155391 q = 1) (hb : d156968 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155391, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155391, d156968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155392 q = 1) (hb : d156969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155392, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155392, d156969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155393 q = 1) (hb : d156970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155393, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155393, d156970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155415 q = 1) (hb : d156992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155415, d156992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155415, d156992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30478 (p : Pattern) (ha : d155421 p = 1) (hb : d156998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155345 q = 1) (hb : d156922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155345, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30460 q ha hb
    | true =>
      simp only [d155345, d156922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30461 q ha hb
  have h2 (q : Pattern) (ha : d155346 q = 1) (hb : d156923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155346, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155346, d156923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155347 q = 1) (hb : d156924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155347, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155347, d156924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155348 q = 1) (hb : d156925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155348, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155348, d156925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155355 q = 1) (hb : d156932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155355, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30462 q ha hb
    | true =>
      simp only [d155355, d156932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30463 q ha hb
  have h6 (q : Pattern) (ha : d155356 q = 1) (hb : d156933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155356, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155356, d156933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155357 q = 1) (hb : d156934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155357, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155357, d156934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155389 q = 1) (hb : d156966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155389, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30469 q ha hb
    | true =>
      simp only [d155389, d156966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155390 q = 1) (hb : d156967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155390, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155390, d156967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155395 q = 1) (hb : d156972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155395, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30470 q ha hb
    | true =>
      simp only [d155395, d156972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155396 q = 1) (hb : d156973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155396, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155396, d156973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155397 q = 1) (hb : d156974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155397, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155397, d156974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155398 q = 1) (hb : d156975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155398, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155398, d156975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155399 q = 1) (hb : d156976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155399, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155399, d156976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155403 q = 1) (hb : d156980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155403, d156980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30472 q ha hb
    | true =>
      simp only [d155403, d156980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30473 q ha hb
  have h17 (q : Pattern) (ha : d155404 q = 1) (hb : d156981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155404, d156981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155404, d156981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155405 q = 1) (hb : d156982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155405, d156982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155405, d156982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d155406 q = 1) (hb : d156983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155406, d156983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155406, d156983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155409 q = 1) (hb : d156986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155409, d156986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30474 q ha hb
    | true =>
      simp only [d155409, d156986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30475 q ha hb
  have h21 (q : Pattern) (ha : d155410 q = 1) (hb : d156987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155410, d156987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155410, d156987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d155411 q = 1) (hb : d156988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155411, d156988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155411, d156988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155413 q = 1) (hb : d156990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155413, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30476 q ha hb
    | true =>
      simp only [d155413, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30457 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d155332 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d155414 q = 1) (hb : d156991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155414, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d155414, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d155416 q = 1) (hb : d156993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155416, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30477 q ha hb
    | true =>
      simp only [d155416, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d155417 q = 1) (hb : d156994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155417, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d155417, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d155418 q = 1) (hb : d156995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155418, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d155418, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d155419 q = 1) (hb : d156996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155419, d156996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d155419, d156996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d155420 q = 1) (hb : d156997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155420, d156997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155420, d156997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d155421 q = 1) (hb : d156998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155421, d156998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155421, d156998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30479 (p : Pattern) (ha : d155428 p = 1) (hb : d157005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155322 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
    | true =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
  have h2 (q : Pattern) (ha : d155323 q = 1) (hb : d156900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155323, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155324 q = 1) (hb : d156901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155324, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155325 q = 1) (hb : d156902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155325, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155326 q = 1) (hb : d156903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155326, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155423 q = 1) (hb : d157000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155423, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
    | true =>
      simp only [d155423, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155424 q = 1) (hb : d157001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155424, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155424, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155425 q = 1) (hb : d157002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155425, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155425, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155426 q = 1) (hb : d157003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155426, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155426, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155427 q = 1) (hb : d157004 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155427, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155427, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155428 q = 1) (hb : d157005 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155428, d157005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155428, d157005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30480 (p : Pattern) (ha : d155434 p = 1) (hb : d157011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155423 q = 1) (hb : d157000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155423, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
    | true =>
      simp only [d155423, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155424 q = 1) (hb : d157001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155424, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155424, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155425 q = 1) (hb : d157002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155425, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155425, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155426 q = 1) (hb : d157003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155426, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155426, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155427 q = 1) (hb : d157004 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155427, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155427, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155429 q = 1) (hb : d157006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155429, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30458 q ha hb
    | true =>
      simp only [d155429, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155430 q = 1) (hb : d157007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155430, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155430, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155431 q = 1) (hb : d157008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155431, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155431, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155432 q = 1) (hb : d157009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155432, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155432, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155433 q = 1) (hb : d157010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155433, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155433, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155434 q = 1) (hb : d157011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155434, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155434, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30481 (p : Pattern) (ha : d155441 p = 1) (hb : d157018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155413 q = 1) (hb : d156990 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155413, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30476 q ha hb
    | true =>
      simp only [d155413, d156990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30457 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155414 q = 1) (hb : d156991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155414, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155414, d156991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155416 q = 1) (hb : d156993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155416, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30477 q ha hb
    | true =>
      simp only [d155416, d156993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155417 q = 1) (hb : d156994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155417, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155417, d156994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155418 q = 1) (hb : d156995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155418, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155418, d156995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155439 q = 1) (hb : d157016 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155439, d157016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155439, d157016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155440 q = 1) (hb : d157017 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155440, d157017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155440, d157017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155441 q = 1) (hb : d157018 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155441, d157018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155441, d157018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30482 (p : Pattern) (ha : d155443 p = 1) (hb : d157020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155429 q = 1) (hb : d157006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155429, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30458 q ha hb
    | true =>
      simp only [d155429, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155430 q = 1) (hb : d157007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155430, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155430, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155431 q = 1) (hb : d157008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155431, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155431, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155432 q = 1) (hb : d157009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155432, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155432, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155433 q = 1) (hb : d157010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155433, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155433, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155443 q = 1) (hb : d157020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155443, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155443, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30483 (p : Pattern) (ha : d155119 p = 1) (hb : d157046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155114 q = 1) (hb : d156695 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155114, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
  have h2 (q : Pattern) (ha : d155060 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30408 q ha hb
    | true =>
      simp only [d155060, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155115 q = 1) (hb : d156696 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155115, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155061 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155061, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155116 q = 1) (hb : d156697 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155116, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155117 q = 1) (hb : d156698 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155117, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d154999 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155118 q = 1) (hb : d157045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155118, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155118, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155000 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155119 q = 1) (hb : d157046 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155119, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155119, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro30484 (p : Pattern) (ha : d155459 p = 1) (hb : d157031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155449 q = 1) (hb : d157026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155449, d157026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155449, d157026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30464 q ha hb
  have h2 (q : Pattern) (ha : d155360 q = 1) (hb : d156936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155360, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30464 q ha hb
    | true =>
      simp only [d155360, d156936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155450 q = 1) (hb : d157027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155450, d157027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155450, d157027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155361 q = 1) (hb : d156937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155361, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155361, d156937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155451 q = 1) (hb : d157028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155451, d157028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155451, d157028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155452 q = 1) (hb : d157029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155452, d157029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155452, d157029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155251 q = 1) (hb : d156824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155251, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155251, d156824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
  have h8 (q : Pattern) (ha : d155179 q = 1) (hb : d156759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30429 q ha hb
    | true =>
      simp only [d155179, d156759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155252 q = 1) (hb : d156825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155252, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155252, d156825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155180 q = 1) (hb : d156760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155180, d156760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d155253 q = 1) (hb : d156826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155253, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155253, d156826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155254 q = 1) (hb : d156827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155254, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155254, d156827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155453 q = 1) (hb : d157030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155453, d157030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155453, d157030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155458 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155459 q = 1) (hb : d157031 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155459, d157031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155459, d157031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30485 (p : Pattern) (ha : d155463 p = 1) (hb : d157040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155256 q = 1) (hb : d157035 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155256, d157035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155256, d157035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30466 q ha hb
  have h2 (q : Pattern) (ha : d155186 q = 1) (hb : d156948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155186, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30466 q ha hb
    | true =>
      simp only [d155186, d156948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155257 q = 1) (hb : d157036 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155257, d157036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155257, d157036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155187 q = 1) (hb : d156949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155187, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155187, d156949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155258 q = 1) (hb : d157037 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155258, d157037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155258, d157037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155259 q = 1) (hb : d157038 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155259, d157038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155259, d157038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d154999 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155260 q = 1) (hb : d157039 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155260, d157039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155260, d157039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155000 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155463 q = 1) (hb : d157040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155463, d157040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155463, d157040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro30486 (p : Pattern) (ha : d155469 p = 1) (hb : d157055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155460 q = 1) (hb : d157032 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155460, d157032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30484 q ha hb
    | true =>
      simp only [d155460, d157032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30443 q ha hb
  have h2 (q : Pattern) (ha : d155461 q = 1) (hb : d157033 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155461, d157033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155461, d157033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155462 q = 1) (hb : d157034 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155462, d157034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155462, d157034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155464 q = 1) (hb : d157041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155464, d157041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30443 q ha hb
    | true =>
      simp only [d155464, d157041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30485 q ha hb
  have h5 (q : Pattern) (ha : d155465 q = 1) (hb : d157042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155465, d157042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155465, d157042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155466 q = 1) (hb : d157043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155466, d157043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155466, d157043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155467 q = 1) (hb : d157044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155467, d157044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155467, d157044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155262 q = 1) (hb : d157047 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155262, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30443 q ha hb
    | true =>
      simp only [d155262, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30483 q ha hb
  have h9 (q : Pattern) (ha : d155263 q = 1) (hb : d157048 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155263, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155263, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155264 q = 1) (hb : d157049 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155264, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155264, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155001 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155120 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30483 q ha hb
    | true =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d155121 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155122 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155265 q = 1) (hb : d157053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155265, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155265, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155468 q = 1) (hb : d157054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155468, d157054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155468, d157054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155469 q = 1) (hb : d157055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155469, d157055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155469, d157055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro30487 (p : Pattern) (ha : d155474 p = 1) (hb : d157060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155262 q = 1) (hb : d157047 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155262, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30443 q ha hb
    | true =>
      simp only [d155262, d157047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30483 q ha hb
  have h2 (q : Pattern) (ha : d155263 q = 1) (hb : d157048 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155263, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155263, d157048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155264 q = 1) (hb : d157049 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155264, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155264, d157049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155120 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30483 q ha hb
    | true =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155121 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155122 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155265 q = 1) (hb : d157053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155265, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155265, d157053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155472 q = 1) (hb : d157058 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155472, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155472, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155473 q = 1) (hb : d157059 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155473, d157059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155473, d157059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155474 q = 1) (hb : d157060 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155474, d157060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155474, d157060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro30488 (p : Pattern) (ha : d155480 p = 1) (hb : d157066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155470 q = 1) (hb : d157056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155470, d157056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30486 q ha hb
    | true =>
      simp only [d155470, d157056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155471 q = 1) (hb : d157057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155471, d157057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155471, d157057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155475 q = 1) (hb : d157061 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30487 q ha hb
    | true =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155476 q = 1) (hb : d157062 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155477 q = 1) (hb : d157063 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155477, d157063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155477, d157063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155478 q = 1) (hb : d157064 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155478, d157064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155478, d157064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155479 q = 1) (hb : d157065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155479, d157065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155479, d157065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155480 q = 1) (hb : d157066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155480, d157066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155480, d157066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30489 (p : Pattern) (ha : d155482 p = 1) (hb : d157068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155120 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30483 q ha hb
    | true =>
      simp only [d155120, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d155121 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155121, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155122 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155122, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155472 q = 1) (hb : d157058 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155472, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155472, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155481 q = 1) (hb : d157067 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155481, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155481, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155482 q = 1) (hb : d157068 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155482, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155482, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro30490 (p : Pattern) (ha : d155488 p = 1) (hb : d157074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155475 q = 1) (hb : d157061 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30487 q ha hb
    | true =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155476 q = 1) (hb : d157062 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155483 q = 1) (hb : d157069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155483, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30489 q ha hb
    | true =>
      simp only [d155483, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155484 q = 1) (hb : d157070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155484, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155484, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155485 q = 1) (hb : d157071 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155485, d157071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155485, d157071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155486 q = 1) (hb : d157072 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155486, d157072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155486, d157072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155487 q = 1) (hb : d157073 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155487, d157073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155487, d157073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155488 q = 1) (hb : d157074 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155488, d157074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155488, d157074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30491 (p : Pattern) (ha : d155499 p = 1) (hb : d157080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155475 q = 1) (hb : d157061 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30487 q ha hb
    | true =>
      simp only [d155475, d157061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155476 q = 1) (hb : d157062 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155476, d157062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155496 q = 1) (hb : d157077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155496, d157077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155496, d157077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155497 q = 1) (hb : d157078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155497, d157078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155497, d157078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155498 q = 1) (hb : d157079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155498, d157079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155498, d157079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155499 q = 1) (hb : d157080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155499, d157080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155499, d157080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30492 (p : Pattern) (ha : d155505 p = 1) (hb : d157086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155489 q = 1) (hb : d157075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155489, d157075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30488 q ha hb
    | true =>
      simp only [d155489, d157075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30490 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155495 q = 1) (hb : d157076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155495, d157076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155495, d157076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155500 q = 1) (hb : d157081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155500, d157081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30491 q ha hb
    | true =>
      simp only [d155500, d157081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155501 q = 1) (hb : d157082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155501, d157082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155501, d157082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155502 q = 1) (hb : d157083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155502, d157083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155502, d157083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155503 q = 1) (hb : d157084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155503, d157084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155503, d157084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155504 q = 1) (hb : d157085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155504, d157085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155504, d157085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155505 q = 1) (hb : d157086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155505, d157086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155505, d157086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30493 (p : Pattern) (ha : d155493 p = 1) (hb : d157091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155483 q = 1) (hb : d157069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155483, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30489 q ha hb
    | true =>
      simp only [d155483, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155484 q = 1) (hb : d157070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155484, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155484, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155490 q = 1) (hb : d157088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155490, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155490, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155491 q = 1) (hb : d157089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155491, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155491, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155492 q = 1) (hb : d157090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155492, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155492, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155493 q = 1) (hb : d157091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155493, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155493, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30494 (p : Pattern) (ha : d155512 p = 1) (hb : d157097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155507 q = 1) (hb : d157092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155507, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30493 q ha hb
    | true =>
      simp only [d155507, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155508 q = 1) (hb : d157093 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155508, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155508, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155509 q = 1) (hb : d157094 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155509, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155509, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155510 q = 1) (hb : d157095 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155510, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155510, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155511 q = 1) (hb : d157096 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155511, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155511, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155512 q = 1) (hb : d157097 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155512, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155512, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30495 (p : Pattern) (ha : d155518 p = 1) (hb : d157103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155328 q = 1) (hb : d156905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155328, d156905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155328, d156905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30456 q ha hb
  have h2 (q : Pattern) (ha : d155329 q = 1) (hb : d156906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155329, d156906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155329, d156906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155338 q = 1) (hb : d156915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155338, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30456 q ha hb
    | true =>
      simp only [d155338, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30459 q ha hb
  have h4 (q : Pattern) (ha : d155339 q = 1) (hb : d156916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155339, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155339, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155340 q = 1) (hb : d156917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155340, d156917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155340, d156917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155422 q = 1) (hb : d156999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155422, d156999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30471 q ha hb
    | true =>
      simp only [d155422, d156999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30478 q ha hb
  have h7 (q : Pattern) (ha : d155435 q = 1) (hb : d157012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155435, d157012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30479 q ha hb
    | true =>
      simp only [d155435, d157012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30480 q ha hb
  have h8 (q : Pattern) (ha : d155436 q = 1) (hb : d157013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155436, d157013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155436, d157013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155437 q = 1) (hb : d157014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155437, d157014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155437, d157014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155438 q = 1) (hb : d157015 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155438, d157015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155438, d157015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155442 q = 1) (hb : d157019 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155442, d157019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155442, d157019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30481 q ha hb
  have h12 (q : Pattern) (ha : d155444 q = 1) (hb : d157021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155444, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155444, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30482 q ha hb
  have h13 (q : Pattern) (ha : d155445 q = 1) (hb : d157022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155445, d157022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155445, d157022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155446 q = 1) (hb : d157023 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155446, d157023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155446, d157023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d155447 q = 1) (hb : d157024 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155447, d157024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155447, d157024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d155448 q = 1) (hb : d157025 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155448, d157025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155448, d157025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155506 q = 1) (hb : d157087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155506, d157087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155506, d157087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30492 q ha hb
  have h18 (q : Pattern) (ha : d155513 q = 1) (hb : d157098 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155513, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155513, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30494 q ha hb
  have h19 (q : Pattern) (ha : d155514 q = 1) (hb : d157099 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155514, d157099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155514, d157099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155515 q = 1) (hb : d157100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155515, d157100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155515, d157100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d155516 q = 1) (hb : d157101 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155516, d157101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d155516, d157101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d155517 q = 1) (hb : d157102 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155517, d157102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155517, d157102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155518 q = 1) (hb : d157103 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155518, d157103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155518, d157103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30496 (p : Pattern) (ha : d155524 p = 1) (hb : d157109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155519 q = 1) (hb : d157104 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155519, d157104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155519, d157104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30495 q ha hb
  have h2 (q : Pattern) (ha : d155520 q = 1) (hb : d157105 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155520, d157105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155520, d157105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155521 q = 1) (hb : d157106 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155521, d157106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155521, d157106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155522 q = 1) (hb : d157107 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155522, d157107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155522, d157107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155523 q = 1) (hb : d157108 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155523, d157108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155523, d157108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155524 q = 1) (hb : d157109 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155524, d157109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155524, d157109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30497 (p : Pattern) (ha : d155528 p = 1) (hb : d157112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155528 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26079 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d537 q = 1) (hb : d52284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75 q ha hb
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d538 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d25429 q = 1) (hb : d52285 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26087 q = 1) (hb : d155527 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26087, d155527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26087, d155527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26088 q = 1) (hb : d155528 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26088, d155528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26088, d155528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d155528 q = 1) (hb : d157112 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30498 (p : Pattern) (ha : d155534 p = 1) (hb : d157117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155534 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26089 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9796 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26105 q = 1) (hb : d155533 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26105, d155533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26105, d155533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26106 q = 1) (hb : d155534 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26106, d155534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26106, d155534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d155534 q = 1) (hb : d157117 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30499 (p : Pattern) (ha : d155540 p = 1) (hb : d157123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155529 q = 1) (hb : d157113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
    | true =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155530 q = 1) (hb : d157114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155531 q = 1) (hb : d157115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155531, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155531, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155532 q = 1) (hb : d157116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155532, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155532, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155535 q = 1) (hb : d157118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
    | true =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155536 q = 1) (hb : d157119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155537 q = 1) (hb : d157120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155537, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155537, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155538 q = 1) (hb : d157121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155538, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155538, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155539 q = 1) (hb : d157122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155539, d157122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155539, d157122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155371 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155540 q = 1) (hb : d157123 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155540, d157123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155540, d157123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
end NetHack.Soko22Hazard87
