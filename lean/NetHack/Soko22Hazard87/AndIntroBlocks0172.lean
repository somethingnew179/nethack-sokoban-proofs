import NetHack.Soko22Hazard87.AndIntroBlocks0171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro43000 (p : Pattern) (ha : d129225 p = 1) (hb : d181520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19545 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19545, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129194 q = 1) (hb : d181502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129194, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129194, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129195 q = 1) (hb : d181503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129195, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129195, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129196 q = 1) (hb : d181504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129196, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129196, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129225 q = 1) (hb : d181520 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129225, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129225, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro43001 (p : Pattern) (ha : d129231 p = 1) (hb : d181526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129167 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
    | true =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
  have h2 (q : Pattern) (ha : d129168 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129169 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129177 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42993 q ha hb
  have h5 (q : Pattern) (ha : d129178 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129179 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129180 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129226 q = 1) (hb : d181521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129226, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129226, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43000 q ha hb
  have h9 (q : Pattern) (ha : d129227 q = 1) (hb : d181522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129227, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129227, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129228 q = 1) (hb : d181523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129228, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129228, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129229 q = 1) (hb : d181524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129229, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129229, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129230 q = 1) (hb : d181525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129230, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129230, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129231 q = 1) (hb : d181526 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129231, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129231, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro43002 (p : Pattern) (ha : d129237 p = 1) (hb : d181532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129232 q = 1) (hb : d181527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129232, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43001 q ha hb
    | true =>
      simp only [d129232, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129233 q = 1) (hb : d181528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129233, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129233, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129234 q = 1) (hb : d181529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129234, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129234, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129235 q = 1) (hb : d181530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129235, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129235, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129236 q = 1) (hb : d181531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129236, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129236, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129237 q = 1) (hb : d181532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129237, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129237, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43003 (p : Pattern) (ha : d129243 p = 1) (hb : d181538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129210 q = 1) (hb : d181518 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129210, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42996 q ha hb
    | true =>
      simp only [d129210, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42999 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129224 q = 1) (hb : d181519 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129224, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129224, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129238 q = 1) (hb : d181533 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129238, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43002 q ha hb
    | true =>
      simp only [d129238, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129239 q = 1) (hb : d181534 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129239, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129239, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129240 q = 1) (hb : d181535 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129240, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129240, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129241 q = 1) (hb : d181536 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129241, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129241, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129242 q = 1) (hb : d181537 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129242, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129242, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129243 q = 1) (hb : d181538 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129243, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129243, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43004 (p : Pattern) (ha : d129222 p = 1) (hb : d181543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129204 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42998 q ha hb
    | true =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129205 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129219 q = 1) (hb : d181540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129219, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129219, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129220 q = 1) (hb : d181541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129220, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129220, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129221 q = 1) (hb : d181542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129221, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129221, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129222 q = 1) (hb : d181543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129222, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129222, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43005 (p : Pattern) (ha : d129250 p = 1) (hb : d181549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129245 q = 1) (hb : d181544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129245, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43004 q ha hb
    | true =>
      simp only [d129245, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129246 q = 1) (hb : d181545 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129246, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129246, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129247 q = 1) (hb : d181546 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129247, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129247, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129248 q = 1) (hb : d181547 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129248, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129248, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129249 q = 1) (hb : d181548 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129249, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129249, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129250 q = 1) (hb : d181549 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129250, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129250, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43006 (p : Pattern) (ha : d129256 p = 1) (hb : d181555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129244 q = 1) (hb : d181539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129244, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129244, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43003 q ha hb
  have h2 (q : Pattern) (ha : d129251 q = 1) (hb : d181550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129251, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129251, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43005 q ha hb
  have h3 (q : Pattern) (ha : d129252 q = 1) (hb : d181551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129252, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129252, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129253 q = 1) (hb : d181552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129253, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129253, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129254 q = 1) (hb : d181553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129254, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129254, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129255 q = 1) (hb : d181554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129255, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129255, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129256 q = 1) (hb : d181555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129256, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129256, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43007 (p : Pattern) (ha : d129262 p = 1) (hb : d181561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129257 q = 1) (hb : d181556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129257, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129257, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43006 q ha hb
  have h2 (q : Pattern) (ha : d129258 q = 1) (hb : d181557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129258, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129258, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129259 q = 1) (hb : d181558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129259, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129259, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129260 q = 1) (hb : d181559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129260, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129260, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129261 q = 1) (hb : d181560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129261, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129261, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129262 q = 1) (hb : d181561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129262, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129262, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43008 (p : Pattern) (ha : d129268 p = 1) (hb : d181567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128769 q = 1) (hb : d181096 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128769, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42921 q ha hb
    | true =>
      simp only [d128769, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42934 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128859 q = 1) (hb : d181185 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128859, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128859, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42950 q ha hb
  have h3 (q : Pattern) (ha : d128860 q = 1) (hb : d181186 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128860, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128860, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128993 q = 1) (hb : d181310 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128993, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128993, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42969 q ha hb
  have h5 (q : Pattern) (ha : d128994 q = 1) (hb : d181311 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128994, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128994, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128995 q = 1) (hb : d181312 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128995, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128995, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129130 q = 1) (hb : d181438 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129130, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129130, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42988 q ha hb
  have h8 (q : Pattern) (ha : d129131 q = 1) (hb : d181439 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129131, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129131, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129132 q = 1) (hb : d181440 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129132, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129132, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129133 q = 1) (hb : d181441 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129133, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129133, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129263 q = 1) (hb : d181562 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129263, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129263, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43007 q ha hb
  have h12 (q : Pattern) (ha : d129264 q = 1) (hb : d181563 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129264, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129264, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129265 q = 1) (hb : d181564 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129265, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129265, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129266 q = 1) (hb : d181565 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129266, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129266, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129267 q = 1) (hb : d181566 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129267, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129267, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129268 q = 1) (hb : d181567 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129268, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129268, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43009 (p : Pattern) (ha : d129274 p = 1) (hb : d181573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129269 q = 1) (hb : d181568 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129269, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43008 q ha hb
    | true =>
      simp only [d129269, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129270 q = 1) (hb : d181569 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129270, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129270, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129271 q = 1) (hb : d181570 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129271, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129271, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129272 q = 1) (hb : d181571 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129272, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129272, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129273 q = 1) (hb : d181572 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129273, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129273, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129274 q = 1) (hb : d181573 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129274, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129274, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43010 (p : Pattern) (ha : d129280 p = 1) (hb : d181579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129275 q = 1) (hb : d181574 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129275, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43009 q ha hb
    | true =>
      simp only [d129275, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129276 q = 1) (hb : d181575 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129276, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129276, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129277 q = 1) (hb : d181576 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129277, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129277, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129278 q = 1) (hb : d181577 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129278, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129278, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129279 q = 1) (hb : d181578 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129279, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129279, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129280 q = 1) (hb : d181579 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129280, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129280, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43011 (p : Pattern) (ha : d129286 p = 1) (hb : d181585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129281 q = 1) (hb : d181580 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129281, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43010 q ha hb
    | true =>
      simp only [d129281, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129282 q = 1) (hb : d181581 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129282, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129282, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129283 q = 1) (hb : d181582 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129283, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129283, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129284 q = 1) (hb : d181583 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129284, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129284, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129285 q = 1) (hb : d181584 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129285, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129285, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129286 q = 1) (hb : d181585 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129286, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129286, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43012 (p : Pattern) (ha : d129292 p = 1) (hb : d181591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129287 q = 1) (hb : d181586 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129287, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43011 q ha hb
    | true =>
      simp only [d129287, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129288 q = 1) (hb : d181587 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129288, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129288, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129289 q = 1) (hb : d181588 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129289, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129289, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129290 q = 1) (hb : d181589 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129290, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129290, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129291 q = 1) (hb : d181590 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129291, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129291, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129292 q = 1) (hb : d181591 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129292, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129292, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43013 (p : Pattern) (ha : d129298 p = 1) (hb : d181597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129293 q = 1) (hb : d181592 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129293, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43012 q ha hb
    | true =>
      simp only [d129293, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129294 q = 1) (hb : d181593 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129294, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129294, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129295 q = 1) (hb : d181594 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129295, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129295, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129296 q = 1) (hb : d181595 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129296, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129296, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129297 q = 1) (hb : d181596 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129297, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129297, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129298 q = 1) (hb : d181597 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129298, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129298, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43014 (p : Pattern) (ha : d129304 p = 1) (hb : d181603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129299 q = 1) (hb : d181598 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129299, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43013 q ha hb
    | true =>
      simp only [d129299, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129300 q = 1) (hb : d181599 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129300, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129300, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129301 q = 1) (hb : d181600 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129301, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129301, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129302 q = 1) (hb : d181601 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129302, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129302, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129303 q = 1) (hb : d181602 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129303, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129303, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129304 q = 1) (hb : d181603 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129304, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129304, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43015 (p : Pattern) (ha : d129310 p = 1) (hb : d181609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129305 q = 1) (hb : d181604 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129305, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43014 q ha hb
    | true =>
      simp only [d129305, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129306 q = 1) (hb : d181605 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129306, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129306, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129307 q = 1) (hb : d181606 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129307, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129307, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129308 q = 1) (hb : d181607 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129308, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129308, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129309 q = 1) (hb : d181608 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129309, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129309, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129310 q = 1) (hb : d181609 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129310, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129310, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43016 (p : Pattern) (ha : d180908 p = 1) (hb : d187684 p = 1) : d181614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18696 q = 1) (hb : d180908 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42773 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187680 q = 1) : d181610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187680, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187680, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187681 q = 1) : d181611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187681, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187681, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187682 q = 1) : d181612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187682, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187682, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187683 q = 1) : d181613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187683, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187683, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187684 q = 1) : d181614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187684, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187684, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43017 (p : Pattern) (ha : d180908 p = 1) (hb : d187694 p = 1) : d181624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d180908 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42770 q ha hb
    | true =>
      simp only [d18592, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42764 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187690 q = 1) : d181620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187690, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187690, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187691 q = 1) : d181621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187691, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187691, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187692 q = 1) : d181622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187692, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187692, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187693 q = 1) : d181623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187693, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187693, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187694 q = 1) : d181624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187694, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187694, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43018 (p : Pattern) (ha : d180908 p = 1) (hb : d187700 p = 1) : d181630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187695 q = 1) : d181625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187695, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187695, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43017 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187696 q = 1) : d181626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187696, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187696, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187697 q = 1) : d181627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187697, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187697, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187698 q = 1) : d181628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187698, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187698, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187699 q = 1) : d181629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187699, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187699, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187700 q = 1) : d181630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187700, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187700, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43019 (p : Pattern) (ha : d180908 p = 1) (hb : d187706 p = 1) : d181636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187685 q = 1) : d181615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187685, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187685, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43016 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187686 q = 1) : d181616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187686, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187686, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187687 q = 1) : d181617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187687, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187687, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187688 q = 1) : d181618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187688, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187688, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187689 q = 1) : d181619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187689, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187689, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187701 q = 1) : d181631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187701, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187701, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43018 q ha hb
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d187702 q = 1) : d181632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187702, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187702, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d187703 q = 1) : d181633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187703, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187703, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d180908 q = 1) (hb : d187704 q = 1) : d181634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187704, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187704, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180908 q = 1) (hb : d187705 q = 1) : d181635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187705, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187705, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d180908 q = 1) (hb : d187706 q = 1) : d181636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187706, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187706, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43020 (p : Pattern) (ha : d180908 p = 1) (hb : d187712 p = 1) : d181642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187707 q = 1) : d181637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187707, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42792 q hb ha
    | true =>
      simp only [d187707, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42783 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187708 q = 1) : d181638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187708, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187708, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187709 q = 1) : d181639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187709, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187709, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187710 q = 1) : d181640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187710, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187710, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187711 q = 1) : d181641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187711, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187711, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187712 q = 1) : d181642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187712, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187712, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43021 (p : Pattern) (ha : d180908 p = 1) (hb : d187718 p = 1) : d181648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187713 q = 1) : d181643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187713, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187713, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43020 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187714 q = 1) : d181644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187714, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187714, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187715 q = 1) : d181645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187715, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187715, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187716 q = 1) : d181646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187716, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187716, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187717 q = 1) : d181647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187717, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187717, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187718 q = 1) : d181648 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187718, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187718, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43022 (p : Pattern) (ha : d180908 p = 1) (hb : d187724 p = 1) : d181654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187719 q = 1) : d181649 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187719, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187719, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43021 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187720 q = 1) : d181650 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187720, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187720, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187721 q = 1) : d181651 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187721, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187721, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187722 q = 1) : d181652 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187722, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187722, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187723 q = 1) : d181653 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187723, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187723, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187724 q = 1) : d181654 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187724, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187724, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43023 (p : Pattern) (ha : d180908 p = 1) (hb : d187731 p = 1) : d181661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187726 q = 1) : d181656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187726, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42813 q hb ha
    | true =>
      simp only [d187726, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42802 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187727 q = 1) : d181657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187727, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187727, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187728 q = 1) : d181658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187728, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187728, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187729 q = 1) : d181659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187729, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187729, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187730 q = 1) : d181660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187730, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187730, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187731 q = 1) : d181661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187731, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187731, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43024 (p : Pattern) (ha : d180908 p = 1) (hb : d187737 p = 1) : d181667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187732 q = 1) : d181662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187732, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187732, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43023 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187733 q = 1) : d181663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187733, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187733, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187734 q = 1) : d181664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187734, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187734, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187735 q = 1) : d181665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187735, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187735, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187736 q = 1) : d181666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187736, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187736, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187737 q = 1) : d181667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187737, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187737, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43025 (p : Pattern) (ha : d180908 p = 1) (hb : d187743 p = 1) : d181673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187738 q = 1) : d181668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187738, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187738, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43024 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187739 q = 1) : d181669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187739, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187739, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187740 q = 1) : d181670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187740, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187740, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187741 q = 1) : d181671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187741, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187741, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187742 q = 1) : d181672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187742, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187742, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187743 q = 1) : d181673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187743, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187743, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43026 (p : Pattern) (ha : d180908 p = 1) (hb : d187747 p = 1) : d181677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
    | true =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42832 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19083 q = 1) (hb : d180908 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19083, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42821 q ha hb
  have h9 (q : Pattern) (ha : d19084 q = 1) (hb : d180908 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19085 q = 1) (hb : d180908 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19086 q = 1) (hb : d180908 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19086, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d180908 q = 1) (hb : d187746 q = 1) : d181676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187746, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187746, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d16444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
    | true =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
  have h14 (q : Pattern) (ha : d19061 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19062 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16447 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42825 q ha hb
  have h17 (q : Pattern) (ha : d19063 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19064 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19065 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d16451 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42818 q ha hb
  have h21 (q : Pattern) (ha : d19088 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19089 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19090 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d132455 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d187747 q = 1) : d181677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187747, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187747, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro43027 (p : Pattern) (ha : d180908 p = 1) (hb : d187753 p = 1) : d181683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187748 q = 1) : d181678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187748, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43026 q ha hb
    | true =>
      simp only [d187748, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187749 q = 1) : d181679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187749, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187749, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42822 q ha hb
    | true =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187750 q = 1) : d181680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187750, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187750, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187751 q = 1) : d181681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187751, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187751, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d187752 q = 1) : d181682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187752, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187752, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d187753 q = 1) : d181683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187753, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187753, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43028 (p : Pattern) (ha : d180908 p = 1) (hb : d187759 p = 1) : d181689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187754 q = 1) : d181684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187754, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43027 q ha hb
    | true =>
      simp only [d187754, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42823 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187755 q = 1) : d181685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187755, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187755, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187756 q = 1) : d181686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187756, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187756, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187757 q = 1) : d181687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187757, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187757, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187758 q = 1) : d181688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187758, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187758, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187759 q = 1) : d181689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187759, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187759, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43029 (p : Pattern) (ha : d180908 p = 1) (hb : d187765 p = 1) : d181695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187760 q = 1) : d181690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187760, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187760, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43028 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187761 q = 1) : d181691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187761, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187761, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187762 q = 1) : d181692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187762, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187762, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187763 q = 1) : d181693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187763, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187763, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187764 q = 1) : d181694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187764, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187764, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187765 q = 1) : d181695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187765, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187765, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43030 (p : Pattern) (ha : d180908 p = 1) (hb : d187771 p = 1) : d181701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187766 q = 1) : d181696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187766, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187766, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43029 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187767 q = 1) : d181697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187767, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187767, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187768 q = 1) : d181698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187768, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187768, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187769 q = 1) : d181699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187769, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187769, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187770 q = 1) : d181700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187770, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187770, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187771 q = 1) : d181701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187771, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187771, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43031 (p : Pattern) (ha : d180908 p = 1) (hb : d187776 p = 1) : d181706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
    | true =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42858 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19318 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19318, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19318, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42847 q ha hb
  have h9 (q : Pattern) (ha : d19319 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19319, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19320 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19321 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19321, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d180908 q = 1) (hb : d187775 q = 1) : d181705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187775, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187775, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d16796 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
    | true =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
  have h14 (q : Pattern) (ha : d19293 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16799 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42851 q ha hb
  have h17 (q : Pattern) (ha : d19295 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19296 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19297 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d16803 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42844 q ha hb
  have h21 (q : Pattern) (ha : d19323 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19324 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19325 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d132484 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d187776 q = 1) : d181706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187776, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187776, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro43032 (p : Pattern) (ha : d180908 p = 1) (hb : d187782 p = 1) : d181712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187777 q = 1) : d181707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187777, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43031 q ha hb
    | true =>
      simp only [d187777, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187778 q = 1) : d181708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187778, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187778, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42848 q ha hb
    | true =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187779 q = 1) : d181709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187779, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187779, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187780 q = 1) : d181710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187780, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187780, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d187781 q = 1) : d181711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187781, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187781, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d187782 q = 1) : d181712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187782, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187782, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43033 (p : Pattern) (ha : d180908 p = 1) (hb : d187788 p = 1) : d181718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187783 q = 1) : d181713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187783, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43032 q ha hb
    | true =>
      simp only [d187783, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42849 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187784 q = 1) : d181714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187784, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187784, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187785 q = 1) : d181715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187785, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187785, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187786 q = 1) : d181716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187786, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187786, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187787 q = 1) : d181717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187787, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187787, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187788 q = 1) : d181718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187788, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187788, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43034 (p : Pattern) (ha : d180908 p = 1) (hb : d187794 p = 1) : d181724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187789 q = 1) : d181719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187789, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187789, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43033 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187790 q = 1) : d181720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187790, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187790, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187791 q = 1) : d181721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187791, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187791, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187792 q = 1) : d181722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187792, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187792, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187793 q = 1) : d181723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187793, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187793, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187794 q = 1) : d181724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187794, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187794, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43035 (p : Pattern) (ha : d180908 p = 1) (hb : d187800 p = 1) : d181730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187795 q = 1) : d181725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187795, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187795, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43034 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187796 q = 1) : d181726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187796, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187796, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187797 q = 1) : d181727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187797, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187797, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187798 q = 1) : d181728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187798, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187798, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187799 q = 1) : d181729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187799, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187799, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187800 q = 1) : d181730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187800, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187800, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43036 (p : Pattern) (ha : d180908 p = 1) (hb : d187806 p = 1) : d181736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
    | true =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42884 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19550 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19550, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42873 q ha hb
  have h9 (q : Pattern) (ha : d19551 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19552 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19553 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19553, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d180908 q = 1) (hb : d187805 q = 1) : d181735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187805, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187805, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d17162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
    | true =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
  have h14 (q : Pattern) (ha : d19525 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19526 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42877 q ha hb
  have h17 (q : Pattern) (ha : d19527 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19528 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19529 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d17169 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42870 q ha hb
  have h21 (q : Pattern) (ha : d19555 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19556 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19557 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d132514 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d180908 q = 1) (hb : d187806 q = 1) : d181736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187806, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187806, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  exact h25 p ha hb
theorem andIntro43037 (p : Pattern) (ha : d180908 p = 1) (hb : d187812 p = 1) : d181742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187807 q = 1) : d181737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187807, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43036 q ha hb
    | true =>
      simp only [d187807, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187808 q = 1) : d181738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187808, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187808, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42874 q ha hb
    | true =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187809 q = 1) : d181739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187809, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187809, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187810 q = 1) : d181740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187810, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187810, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d187811 q = 1) : d181741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187811, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187811, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d187812 q = 1) : d181742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187812, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187812, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43038 (p : Pattern) (ha : d180908 p = 1) (hb : d187818 p = 1) : d181748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187813 q = 1) : d181743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187813, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43037 q ha hb
    | true =>
      simp only [d187813, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42875 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187814 q = 1) : d181744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187814, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187814, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187815 q = 1) : d181745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187815, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187815, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187816 q = 1) : d181746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187816, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187816, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187817 q = 1) : d181747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187817, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187817, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187818 q = 1) : d181748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187818, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187818, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43039 (p : Pattern) (ha : d180908 p = 1) (hb : d187824 p = 1) : d181754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187819 q = 1) : d181749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187819, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187819, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43038 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187820 q = 1) : d181750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187820, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187820, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187821 q = 1) : d181751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187821, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187821, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187822 q = 1) : d181752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187822, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187822, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187823 q = 1) : d181753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187823, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187823, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187824 q = 1) : d181754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187824, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187824, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43040 (p : Pattern) (ha : d180908 p = 1) (hb : d187830 p = 1) : d181760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187825 q = 1) : d181755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187825, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187825, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43039 q ha hb
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187826 q = 1) : d181756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187826, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187826, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187827 q = 1) : d181757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187827, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187827, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187828 q = 1) : d181758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187828, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187828, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187829 q = 1) : d181759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187829, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187829, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187830 q = 1) : d181760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187830, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187830, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43041 (p : Pattern) (ha : d180908 p = 1) (hb : d187836 p = 1) : d181766 p = 1 := by
  have h0 (q : Pattern) (ha : d180908 q = 1) (hb : d187725 q = 1) : d181655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187725, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43019 q ha hb
    | true =>
      simp only [d187725, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43022 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187744 q = 1) : d181674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187744, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187744, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43025 q ha hb
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187745 q = 1) : d181675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187745, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187745, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187772 q = 1) : d181702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187772, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187772, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43030 q ha hb
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187773 q = 1) : d181703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187773, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187773, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187774 q = 1) : d181704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187774, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187774, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d180908 q = 1) (hb : d187801 q = 1) : d181731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187801, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187801, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43035 q ha hb
  have h8 (q : Pattern) (ha : d180908 q = 1) (hb : d187802 q = 1) : d181732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187802, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187802, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d180908 q = 1) (hb : d187803 q = 1) : d181733 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187803, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187803, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d180908 q = 1) (hb : d187804 q = 1) : d181734 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187804, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187804, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d180908 q = 1) (hb : d187831 q = 1) : d181761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187831, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187831, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43040 q ha hb
  have h12 (q : Pattern) (ha : d180908 q = 1) (hb : d187832 q = 1) : d181762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187832, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187832, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d180908 q = 1) (hb : d187833 q = 1) : d181763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187833, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187833, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d180908 q = 1) (hb : d187834 q = 1) : d181764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187834, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187834, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d180908 q = 1) (hb : d187835 q = 1) : d181765 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d187835, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d187835, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d180908 q = 1) (hb : d187836 q = 1) : d181766 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d187836, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d187836, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43042 (p : Pattern) (ha : d180908 p = 1) (hb : d187842 p = 1) : d181772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187837 q = 1) : d181767 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d187837, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43041 q ha hb
    | true =>
      simp only [d187837, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187838 q = 1) : d181768 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d187838, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187838, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187839 q = 1) : d181769 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d187839, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187839, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187840 q = 1) : d181770 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d187840, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187840, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187841 q = 1) : d181771 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d187841, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187841, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187842 q = 1) : d181772 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d187842, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187842, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43043 (p : Pattern) (ha : d180908 p = 1) (hb : d187848 p = 1) : d181778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187843 q = 1) : d181773 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d187843, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43042 q ha hb
    | true =>
      simp only [d187843, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187844 q = 1) : d181774 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d187844, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187844, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187845 q = 1) : d181775 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d187845, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187845, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187846 q = 1) : d181776 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d187846, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187846, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187847 q = 1) : d181777 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d187847, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187847, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187848 q = 1) : d181778 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d187848, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187848, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43044 (p : Pattern) (ha : d180908 p = 1) (hb : d187854 p = 1) : d181784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187849 q = 1) : d181779 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d187849, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43043 q ha hb
    | true =>
      simp only [d187849, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187850 q = 1) : d181780 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d187850, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187850, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187851 q = 1) : d181781 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d187851, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187851, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187852 q = 1) : d181782 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d187852, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187852, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187853 q = 1) : d181783 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d187853, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187853, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187854 q = 1) : d181784 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d187854, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187854, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43045 (p : Pattern) (ha : d180908 p = 1) (hb : d187860 p = 1) : d181790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187855 q = 1) : d181785 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d187855, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43044 q ha hb
    | true =>
      simp only [d187855, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187856 q = 1) : d181786 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d187856, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187856, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187857 q = 1) : d181787 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d187857, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187857, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187858 q = 1) : d181788 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d187858, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187858, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187859 q = 1) : d181789 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d187859, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187859, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187860 q = 1) : d181790 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d187860, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187860, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43046 (p : Pattern) (ha : d180908 p = 1) (hb : d187866 p = 1) : d181796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187861 q = 1) : d181791 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d187861, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43045 q ha hb
    | true =>
      simp only [d187861, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187862 q = 1) : d181792 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d187862, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187862, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187863 q = 1) : d181793 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d187863, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187863, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187864 q = 1) : d181794 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d187864, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187864, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187865 q = 1) : d181795 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d187865, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187865, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187866 q = 1) : d181796 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d187866, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187866, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43047 (p : Pattern) (ha : d180908 p = 1) (hb : d187872 p = 1) : d181802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187867 q = 1) : d181797 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d187867, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43046 q ha hb
    | true =>
      simp only [d187867, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187868 q = 1) : d181798 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d187868, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187868, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187869 q = 1) : d181799 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d187869, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187869, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187870 q = 1) : d181800 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d187870, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187870, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187871 q = 1) : d181801 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d187871, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187871, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187872 q = 1) : d181802 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d187872, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187872, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43048 (p : Pattern) (ha : d180908 p = 1) (hb : d187878 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d180908 q = 1) (hb : d187873 q = 1) : d181803 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d187873, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43047 q ha hb
    | true =>
      simp only [d187873, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d180908 q = 1) (hb : d187874 q = 1) : d181804 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d187874, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187874, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d180908 q = 1) (hb : d187875 q = 1) : d181805 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d187875, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187875, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d180908 q = 1) (hb : d187876 q = 1) : d181806 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d187876, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187876, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d180908 q = 1) (hb : d187877 q = 1) : d181807 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d187877, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187877, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d180908 q = 1) (hb : d187878 q = 1) : d181808 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d187878, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187878, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43049 (p : Pattern) (ha : d128634 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128597 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
    | true =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128630 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128630, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128630, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128598 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128631 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128631, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128631, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128632 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128632, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128632, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128633 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128633, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128633, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128634 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128634, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128634, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43050 (p : Pattern) (ha : d128640 p = 1) (hb : d181614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128635 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128635, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128635, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43049 q ha hb
  have h2 (q : Pattern) (ha : d128636 q = 1) (hb : d181610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128636, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128636, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128637 q = 1) (hb : d181611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128637, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128637, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128638 q = 1) (hb : d181612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128638, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128638, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128639 q = 1) (hb : d181613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128639, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128639, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128640 q = 1) (hb : d181614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128640, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128640, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43051 (p : Pattern) (ha : d128676 p = 1) (hb : d181624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128665 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128629 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128629, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42911 q ha hb
    | true =>
      simp only [d128629, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
  have h3 (q : Pattern) (ha : d128666 q = 1) (hb : d181620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128666, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128666, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128672 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128673 q = 1) (hb : d181621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128673, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128673, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128674 q = 1) (hb : d181622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128674, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128674, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128675 q = 1) (hb : d181623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128675, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128675, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128676 q = 1) (hb : d181624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128676, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128676, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43052 (p : Pattern) (ha : d128688 p = 1) (hb : d181630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128677 q = 1) (hb : d181625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128677, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128677, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43051 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128684 q = 1) (hb : d181626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128684, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128684, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128685 q = 1) (hb : d181627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128685, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128685, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128686 q = 1) (hb : d181628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128686, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128686, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128687 q = 1) (hb : d181629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128687, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128687, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128688 q = 1) (hb : d181630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128688, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128688, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43053 (p : Pattern) (ha : d128694 p = 1) (hb : d181636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128641 q = 1) (hb : d181615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128641, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128641, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43050 q ha hb
  have h3 (q : Pattern) (ha : d128642 q = 1) (hb : d181616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128642, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128642, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128643 q = 1) (hb : d181617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128643, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128643, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128644 q = 1) (hb : d181618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128644, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128644, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128645 q = 1) (hb : d181619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128645, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128645, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128689 q = 1) (hb : d181631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128689, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128689, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43052 q ha hb
  have h8 (q : Pattern) (ha : d128690 q = 1) (hb : d181632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128690, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128690, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128691 q = 1) (hb : d181633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128691, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128691, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128692 q = 1) (hb : d181634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128692, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128692, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128693 q = 1) (hb : d181635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128693, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128693, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128694 q = 1) (hb : d181636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128694, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128694, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43054 (p : Pattern) (ha : d128749 p = 1) (hb : d181642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128738 q = 1) (hb : d181637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128738, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42928 q ha hb
    | true =>
      simp only [d128738, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42931 q ha hb
  have h3 (q : Pattern) (ha : d128739 q = 1) (hb : d181638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128739, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128739, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128745 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128746 q = 1) (hb : d181639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128746, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128746, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128747 q = 1) (hb : d181640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128747, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128747, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128748 q = 1) (hb : d181641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128748, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128748, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128749 q = 1) (hb : d181642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128749, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128749, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43055 (p : Pattern) (ha : d128762 p = 1) (hb : d181648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128750 q = 1) (hb : d181643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128750, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128750, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43054 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128758 q = 1) (hb : d181644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128758, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128758, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128759 q = 1) (hb : d181645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128759, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128759, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128760 q = 1) (hb : d181646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128760, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128760, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128761 q = 1) (hb : d181647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128761, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128761, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128762 q = 1) (hb : d181648 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128762, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128762, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43056 (p : Pattern) (ha : d128768 p = 1) (hb : d181654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128763 q = 1) (hb : d181649 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128763, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128763, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43055 q ha hb
  have h2 (q : Pattern) (ha : d128764 q = 1) (hb : d181650 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128764, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128764, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128765 q = 1) (hb : d181651 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128765, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128765, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128766 q = 1) (hb : d181652 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128766, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128766, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128767 q = 1) (hb : d181653 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128767, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128767, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128768 q = 1) (hb : d181654 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128768, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128768, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43057 (p : Pattern) (ha : d128839 p = 1) (hb : d181661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128828 q = 1) (hb : d181656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128828, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42944 q ha hb
    | true =>
      simp only [d128828, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42947 q ha hb
  have h3 (q : Pattern) (ha : d128829 q = 1) (hb : d181657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128829, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128829, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128836 q = 1) (hb : d181658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128836, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128836, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128837 q = 1) (hb : d181659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128837, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128837, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128838 q = 1) (hb : d181660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128838, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128838, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128839 q = 1) (hb : d181661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128839, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128839, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43058 (p : Pattern) (ha : d128852 p = 1) (hb : d181667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128840 q = 1) (hb : d181662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128840, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128840, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43057 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128848 q = 1) (hb : d181663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128848, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128848, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128849 q = 1) (hb : d181664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128849, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128849, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128850 q = 1) (hb : d181665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128850, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128850, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128851 q = 1) (hb : d181666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128851, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128851, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128852 q = 1) (hb : d181667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128852, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128852, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43059 (p : Pattern) (ha : d128858 p = 1) (hb : d181673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128853 q = 1) (hb : d181668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128853, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128853, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43058 q ha hb
  have h2 (q : Pattern) (ha : d128854 q = 1) (hb : d181669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128854, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128854, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128855 q = 1) (hb : d181670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128855, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128855, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128856 q = 1) (hb : d181671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128856, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128856, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128857 q = 1) (hb : d181672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128857, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128857, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128858 q = 1) (hb : d181673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128858, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128858, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43060 (p : Pattern) (ha : d128942 p = 1) (hb : d181677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128899 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
    | true =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
  have h2 (q : Pattern) (ha : d128900 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128901 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128909 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42955 q ha hb
  have h5 (q : Pattern) (ha : d128910 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128911 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128912 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128928 q = 1) (hb : d181254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128928, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128928, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42959 q ha hb
  have h9 (q : Pattern) (ha : d128929 q = 1) (hb : d181255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128929, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128929, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128930 q = 1) (hb : d181256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128930, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128930, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128931 q = 1) (hb : d181257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128931, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128931, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128941 q = 1) (hb : d181676 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128941, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128941, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128942 q = 1) (hb : d181677 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128942, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128942, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro43061 (p : Pattern) (ha : d128948 p = 1) (hb : d181683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128943 q = 1) (hb : d181678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128943, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43060 q ha hb
    | true =>
      simp only [d128943, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128944 q = 1) (hb : d181679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128944, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128944, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128934 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42960 q ha hb
    | true =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128935 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128945 q = 1) (hb : d181680 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128945, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128945, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128946 q = 1) (hb : d181681 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128946, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128946, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128947 q = 1) (hb : d181682 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128947, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128947, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128948 q = 1) (hb : d181683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128948, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128948, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43062 (p : Pattern) (ha : d128973 p = 1) (hb : d181689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128953 q = 1) (hb : d181684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128953, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43061 q ha hb
    | true =>
      simp only [d128953, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42966 q ha hb
  have h3 (q : Pattern) (ha : d128954 q = 1) (hb : d181685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128954, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128954, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128969 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128970 q = 1) (hb : d181686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128970, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128970, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128971 q = 1) (hb : d181687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128971, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128971, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128972 q = 1) (hb : d181688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128972, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128972, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128973 q = 1) (hb : d181689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128973, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128973, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43063 (p : Pattern) (ha : d128986 p = 1) (hb : d181695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128974 q = 1) (hb : d181690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128974, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128974, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43062 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128982 q = 1) (hb : d181691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128982, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128982, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128983 q = 1) (hb : d181692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128983, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128983, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128984 q = 1) (hb : d181693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128984, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128984, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128985 q = 1) (hb : d181694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128985, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128985, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128986 q = 1) (hb : d181695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128986, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128986, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43064 (p : Pattern) (ha : d128992 p = 1) (hb : d181701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128987 q = 1) (hb : d181696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128987, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128987, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43063 q ha hb
  have h2 (q : Pattern) (ha : d128988 q = 1) (hb : d181697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128988, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128988, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128989 q = 1) (hb : d181698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128989, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128989, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128990 q = 1) (hb : d181699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128990, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128990, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128991 q = 1) (hb : d181700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128991, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128991, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128992 q = 1) (hb : d181701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128992, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128992, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43065 (p : Pattern) (ha : d129079 p = 1) (hb : d181706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129034 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
    | true =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
  have h2 (q : Pattern) (ha : d129035 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129036 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129044 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42974 q ha hb
  have h5 (q : Pattern) (ha : d129045 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129046 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129047 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129065 q = 1) (hb : d181382 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129065, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129065, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42978 q ha hb
  have h9 (q : Pattern) (ha : d129066 q = 1) (hb : d181383 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129066, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129066, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129067 q = 1) (hb : d181384 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129067, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129067, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129068 q = 1) (hb : d181385 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129068, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129068, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129078 q = 1) (hb : d181705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129078, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129078, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129079 q = 1) (hb : d181706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129079, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129079, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro43066 (p : Pattern) (ha : d129085 p = 1) (hb : d181712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129080 q = 1) (hb : d181707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129080, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43065 q ha hb
    | true =>
      simp only [d129080, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129081 q = 1) (hb : d181708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129081, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129081, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129071 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42979 q ha hb
    | true =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129072 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129082 q = 1) (hb : d181709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129082, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129082, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129083 q = 1) (hb : d181710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129083, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129083, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129084 q = 1) (hb : d181711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129084, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129084, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129085 q = 1) (hb : d181712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129085, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129085, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43067 (p : Pattern) (ha : d129110 p = 1) (hb : d181718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129077 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129090 q = 1) (hb : d181713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129090, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43066 q ha hb
    | true =>
      simp only [d129090, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42985 q ha hb
  have h3 (q : Pattern) (ha : d129091 q = 1) (hb : d181714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129091, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129091, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129106 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129107 q = 1) (hb : d181715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129107, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129107, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129108 q = 1) (hb : d181716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129108, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129108, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129109 q = 1) (hb : d181717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129109, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129109, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129110 q = 1) (hb : d181718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129110, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129110, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43068 (p : Pattern) (ha : d129123 p = 1) (hb : d181724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129111 q = 1) (hb : d181719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129111, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129111, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129119 q = 1) (hb : d181720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129119, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129119, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129120 q = 1) (hb : d181721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129120, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129120, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129121 q = 1) (hb : d181722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129121, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129121, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129122 q = 1) (hb : d181723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129122, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129122, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129123 q = 1) (hb : d181724 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129123, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129123, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43069 (p : Pattern) (ha : d129129 p = 1) (hb : d181730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129124 q = 1) (hb : d181725 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129124, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129124, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43068 q ha hb
  have h2 (q : Pattern) (ha : d129125 q = 1) (hb : d181726 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129125, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129125, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129126 q = 1) (hb : d181727 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129126, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129126, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129127 q = 1) (hb : d181728 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129127, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129127, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129128 q = 1) (hb : d181729 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129128, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129128, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129129 q = 1) (hb : d181730 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129129, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129129, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43070 (p : Pattern) (ha : d129212 p = 1) (hb : d181736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129167 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
    | true =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
  have h2 (q : Pattern) (ha : d129168 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129169 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129177 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42993 q ha hb
  have h5 (q : Pattern) (ha : d129178 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129179 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129180 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129198 q = 1) (hb : d181506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129198, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129198, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42997 q ha hb
  have h9 (q : Pattern) (ha : d129199 q = 1) (hb : d181507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129199, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129199, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129200 q = 1) (hb : d181508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129200, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129200, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129201 q = 1) (hb : d181509 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129201, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129201, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129211 q = 1) (hb : d181735 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129211, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129211, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129212 q = 1) (hb : d181736 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129212, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129212, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro43071 (p : Pattern) (ha : d129218 p = 1) (hb : d181742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129213 q = 1) (hb : d181737 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129213, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43070 q ha hb
    | true =>
      simp only [d129213, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129214 q = 1) (hb : d181738 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129214, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129214, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129204 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42998 q ha hb
    | true =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129205 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129215 q = 1) (hb : d181739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129215, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129215, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129216 q = 1) (hb : d181740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129216, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129216, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129217 q = 1) (hb : d181741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129217, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129217, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129218 q = 1) (hb : d181742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129218, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129218, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43072 (p : Pattern) (ha : d129243 p = 1) (hb : d181748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129210 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129223 q = 1) (hb : d181743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129223, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43071 q ha hb
    | true =>
      simp only [d129223, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43004 q ha hb
  have h3 (q : Pattern) (ha : d129224 q = 1) (hb : d181744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129224, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129224, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129240 q = 1) (hb : d181745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129240, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129240, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129241 q = 1) (hb : d181746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129241, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129241, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129242 q = 1) (hb : d181747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129242, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129242, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129243 q = 1) (hb : d181748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129243, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129243, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43073 (p : Pattern) (ha : d129256 p = 1) (hb : d181754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129244 q = 1) (hb : d181749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129244, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129244, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43072 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129251 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129252 q = 1) (hb : d181750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129252, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129252, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129253 q = 1) (hb : d181751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129253, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129253, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129254 q = 1) (hb : d181752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129254, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129254, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129255 q = 1) (hb : d181753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129255, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129255, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129256 q = 1) (hb : d181754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129256, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129256, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43074 (p : Pattern) (ha : d129262 p = 1) (hb : d181760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129257 q = 1) (hb : d181755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129257, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129257, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43073 q ha hb
  have h2 (q : Pattern) (ha : d129258 q = 1) (hb : d181756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129258, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129258, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129259 q = 1) (hb : d181757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129259, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129259, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129260 q = 1) (hb : d181758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129260, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129260, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129261 q = 1) (hb : d181759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129261, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129261, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129262 q = 1) (hb : d181760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129262, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129262, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43075 (p : Pattern) (ha : d129268 p = 1) (hb : d181766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128769 q = 1) (hb : d181655 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128769, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43053 q ha hb
    | true =>
      simp only [d128769, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43056 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128859 q = 1) (hb : d181674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128859, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128859, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43059 q ha hb
  have h3 (q : Pattern) (ha : d128860 q = 1) (hb : d181675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128860, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128860, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128993 q = 1) (hb : d181702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128993, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128993, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43064 q ha hb
  have h5 (q : Pattern) (ha : d128994 q = 1) (hb : d181703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128994, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128994, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128995 q = 1) (hb : d181704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128995, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128995, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129130 q = 1) (hb : d181731 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129130, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129130, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43069 q ha hb
  have h8 (q : Pattern) (ha : d129131 q = 1) (hb : d181732 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129131, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129131, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129132 q = 1) (hb : d181733 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129132, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129132, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129133 q = 1) (hb : d181734 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129133, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129133, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129263 q = 1) (hb : d181761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129263, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129263, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43074 q ha hb
  have h12 (q : Pattern) (ha : d129264 q = 1) (hb : d181762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129264, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129264, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129265 q = 1) (hb : d181763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129265, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129265, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129266 q = 1) (hb : d181764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129266, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129266, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129267 q = 1) (hb : d181765 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129267, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129267, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129268 q = 1) (hb : d181766 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129268, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129268, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43076 (p : Pattern) (ha : d129274 p = 1) (hb : d181772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129269 q = 1) (hb : d181767 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129269, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43075 q ha hb
    | true =>
      simp only [d129269, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129270 q = 1) (hb : d181768 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129270, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129270, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129271 q = 1) (hb : d181769 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129271, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129271, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129272 q = 1) (hb : d181770 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129272, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129272, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129273 q = 1) (hb : d181771 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129273, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129273, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129274 q = 1) (hb : d181772 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129274, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129274, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43077 (p : Pattern) (ha : d129280 p = 1) (hb : d181778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129275 q = 1) (hb : d181773 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129275, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43076 q ha hb
    | true =>
      simp only [d129275, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129276 q = 1) (hb : d181774 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129276, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129276, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129277 q = 1) (hb : d181775 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129277, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129277, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129278 q = 1) (hb : d181776 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129278, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129278, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129279 q = 1) (hb : d181777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129279, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129279, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129280 q = 1) (hb : d181778 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129280, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129280, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43078 (p : Pattern) (ha : d129286 p = 1) (hb : d181784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129281 q = 1) (hb : d181779 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129281, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43077 q ha hb
    | true =>
      simp only [d129281, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129282 q = 1) (hb : d181780 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129282, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129282, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129283 q = 1) (hb : d181781 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129283, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129283, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129284 q = 1) (hb : d181782 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129284, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129284, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129285 q = 1) (hb : d181783 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129285, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129285, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129286 q = 1) (hb : d181784 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129286, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129286, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43079 (p : Pattern) (ha : d129292 p = 1) (hb : d181790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129287 q = 1) (hb : d181785 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129287, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43078 q ha hb
    | true =>
      simp only [d129287, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129288 q = 1) (hb : d181786 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129288, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129288, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129289 q = 1) (hb : d181787 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129289, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129289, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129290 q = 1) (hb : d181788 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129290, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129290, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129291 q = 1) (hb : d181789 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129291, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129291, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129292 q = 1) (hb : d181790 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129292, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129292, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43080 (p : Pattern) (ha : d129298 p = 1) (hb : d181796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129293 q = 1) (hb : d181791 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129293, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43079 q ha hb
    | true =>
      simp only [d129293, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129294 q = 1) (hb : d181792 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129294, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129294, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129295 q = 1) (hb : d181793 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129295, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129295, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129296 q = 1) (hb : d181794 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129296, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129296, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129297 q = 1) (hb : d181795 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129297, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129297, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129298 q = 1) (hb : d181796 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129298, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129298, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43081 (p : Pattern) (ha : d129304 p = 1) (hb : d181802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129299 q = 1) (hb : d181797 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129299, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43080 q ha hb
    | true =>
      simp only [d129299, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129300 q = 1) (hb : d181798 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129300, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129300, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129301 q = 1) (hb : d181799 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129301, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129301, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129302 q = 1) (hb : d181800 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129302, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129302, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129303 q = 1) (hb : d181801 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129303, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129303, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129304 q = 1) (hb : d181802 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129304, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129304, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43082 (p : Pattern) (ha : d129310 p = 1) (hb : d181808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129305 q = 1) (hb : d181803 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129305, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43081 q ha hb
    | true =>
      simp only [d129305, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129306 q = 1) (hb : d181804 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129306, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129306, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129307 q = 1) (hb : d181805 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129307, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129307, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129308 q = 1) (hb : d181806 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129308, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129308, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129309 q = 1) (hb : d181807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129309, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129309, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129310 q = 1) (hb : d181808 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129310, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129310, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43083 (p : Pattern) (ha : d60563 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d60559 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d60559, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d60559, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d60560 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d60560, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60560, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d60561 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d60561, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60561, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60562 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d60562, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60562, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60563 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60563, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60563, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43084 (p : Pattern) (ha : d60569 p = 1) (hb : d181614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60564 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d60564, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60564, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43083 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d181610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60565, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d181611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d181612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d181613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d181614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43085 (p : Pattern) (ha : d129315 p = 1) (hb : d181624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129311 q = 1) (hb : d181620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129311, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129311, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129312 q = 1) (hb : d181621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129312, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129312, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129313 q = 1) (hb : d181622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129313, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129313, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129314 q = 1) (hb : d181623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129314, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129314, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129315 q = 1) (hb : d181624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129315, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129315, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43086 (p : Pattern) (ha : d129321 p = 1) (hb : d181630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129316 q = 1) (hb : d181625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129316, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129316, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129317 q = 1) (hb : d181626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129317, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129317, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129318 q = 1) (hb : d181627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129318, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129318, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129319 q = 1) (hb : d181628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129319, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129319, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129320 q = 1) (hb : d181629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129320, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129320, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129321 q = 1) (hb : d181630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129321, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129321, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43087 (p : Pattern) (ha : d129327 p = 1) (hb : d181636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d60570 q = 1) (hb : d181615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60570, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43084 q ha hb
  have h3 (q : Pattern) (ha : d60571 q = 1) (hb : d181616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60571, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d60572 q = 1) (hb : d181617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60572, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60573 q = 1) (hb : d181618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60573, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60574 q = 1) (hb : d181619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d60574, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129322 q = 1) (hb : d181631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129322, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129322, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43086 q ha hb
  have h8 (q : Pattern) (ha : d129323 q = 1) (hb : d181632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129323, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129323, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129324 q = 1) (hb : d181633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129324, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129324, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129325 q = 1) (hb : d181634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129325, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129325, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129326 q = 1) (hb : d181635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129326, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129326, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129327 q = 1) (hb : d181636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129327, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129327, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43088 (p : Pattern) (ha : d129332 p = 1) (hb : d181642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129328 q = 1) (hb : d181638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129328, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17783 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129329 q = 1) (hb : d181639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129329, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129330 q = 1) (hb : d181640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129330, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129331 q = 1) (hb : d181641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129331, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129332 q = 1) (hb : d181642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129332, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43089 (p : Pattern) (ha : d129338 p = 1) (hb : d181648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129333 q = 1) (hb : d181643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129333, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43088 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129334 q = 1) (hb : d181644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129335 q = 1) (hb : d181645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129336 q = 1) (hb : d181646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129337 q = 1) (hb : d181647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129338 q = 1) (hb : d181648 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129338, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43090 (p : Pattern) (ha : d129344 p = 1) (hb : d181654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129339 q = 1) (hb : d181649 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129339, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43089 q ha hb
  have h2 (q : Pattern) (ha : d129340 q = 1) (hb : d181650 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129340, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129341 q = 1) (hb : d181651 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129341, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129342 q = 1) (hb : d181652 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129342, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129343 q = 1) (hb : d181653 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129343, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129344 q = 1) (hb : d181654 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129344, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43091 (p : Pattern) (ha : d129350 p = 1) (hb : d181661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17865 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181656 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129346 q = 1) (hb : d181657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129346, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17912 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129347 q = 1) (hb : d181658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129347, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129348 q = 1) (hb : d181659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129348, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129349 q = 1) (hb : d181660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129349, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129350 q = 1) (hb : d181661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129350, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43092 (p : Pattern) (ha : d129356 p = 1) (hb : d181667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129351 q = 1) (hb : d181662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129351, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43091 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129352 q = 1) (hb : d181663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129353 q = 1) (hb : d181664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129354 q = 1) (hb : d181665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129355 q = 1) (hb : d181666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129356 q = 1) (hb : d181667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129356, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43093 (p : Pattern) (ha : d129362 p = 1) (hb : d181673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129357 q = 1) (hb : d181668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129357, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43092 q ha hb
  have h2 (q : Pattern) (ha : d129358 q = 1) (hb : d181669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129358, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129359 q = 1) (hb : d181670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129359, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129360 q = 1) (hb : d181671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129360, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129361 q = 1) (hb : d181672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129361, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129362 q = 1) (hb : d181673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129362, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43094 (p : Pattern) (ha : d129369 p = 1) (hb : d181689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181684 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129365 q = 1) (hb : d181685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129365, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129366 q = 1) (hb : d181686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129366, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129367 q = 1) (hb : d181687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129367, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129368 q = 1) (hb : d181688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129368, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129369 q = 1) (hb : d181689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129369, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43095 (p : Pattern) (ha : d129375 p = 1) (hb : d181695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129370 q = 1) (hb : d181690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129370, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43094 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129371 q = 1) (hb : d181691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129372 q = 1) (hb : d181692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129373 q = 1) (hb : d181693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129374 q = 1) (hb : d181694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129375 q = 1) (hb : d181695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129375, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43096 (p : Pattern) (ha : d129381 p = 1) (hb : d181701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129376 q = 1) (hb : d181696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129376, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43095 q ha hb
  have h2 (q : Pattern) (ha : d129377 q = 1) (hb : d181697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129377, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129378 q = 1) (hb : d181698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129378, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129379 q = 1) (hb : d181699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129379, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129380 q = 1) (hb : d181700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129380, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129381 q = 1) (hb : d181701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129381, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43097 (p : Pattern) (ha : d129389 p = 1) (hb : d181718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129385 q = 1) (hb : d181714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129385, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129386 q = 1) (hb : d181715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129386, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129387 q = 1) (hb : d181716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129387, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129388 q = 1) (hb : d181717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129388, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129389 q = 1) (hb : d181718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129389, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43098 (p : Pattern) (ha : d129395 p = 1) (hb : d181724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129390 q = 1) (hb : d181719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129390, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43097 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18293 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129391 q = 1) (hb : d181720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129392 q = 1) (hb : d181721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129393 q = 1) (hb : d181722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129394 q = 1) (hb : d181723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129395 q = 1) (hb : d181724 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129395, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43099 (p : Pattern) (ha : d129401 p = 1) (hb : d181730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129396 q = 1) (hb : d181725 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129396, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43098 q ha hb
  have h2 (q : Pattern) (ha : d129397 q = 1) (hb : d181726 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129397, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129398 q = 1) (hb : d181727 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129398, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129399 q = 1) (hb : d181728 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129399, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129400 q = 1) (hb : d181729 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129400, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129401 q = 1) (hb : d181730 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129401, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43100 (p : Pattern) (ha : d129410 p = 1) (hb : d181748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129406 q = 1) (hb : d181744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129406, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18458 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129407 q = 1) (hb : d181745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129407, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129408 q = 1) (hb : d181746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129408, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129409 q = 1) (hb : d181747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129409, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129410 q = 1) (hb : d181748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129410, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43101 (p : Pattern) (ha : d129416 p = 1) (hb : d181754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129411 q = 1) (hb : d181749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129411, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43100 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129412 q = 1) (hb : d181750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129413 q = 1) (hb : d181751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129414 q = 1) (hb : d181752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129415 q = 1) (hb : d181753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129416 q = 1) (hb : d181754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129416, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43102 (p : Pattern) (ha : d129422 p = 1) (hb : d181760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129417 q = 1) (hb : d181755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129417, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43101 q ha hb
  have h2 (q : Pattern) (ha : d129418 q = 1) (hb : d181756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129418, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129419 q = 1) (hb : d181757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129419, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129420 q = 1) (hb : d181758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129420, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129421 q = 1) (hb : d181759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129421, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129422 q = 1) (hb : d181760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129422, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43103 (p : Pattern) (ha : d129428 p = 1) (hb : d181766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129345 q = 1) (hb : d181655 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43087 q ha hb
    | true =>
      simp only [d129345, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43090 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129363 q = 1) (hb : d181674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129363, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43093 q ha hb
  have h3 (q : Pattern) (ha : d129364 q = 1) (hb : d181675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129382 q = 1) (hb : d181702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129382, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43096 q ha hb
  have h5 (q : Pattern) (ha : d129383 q = 1) (hb : d181703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129383, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129384 q = 1) (hb : d181704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129402 q = 1) (hb : d181731 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129402, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43099 q ha hb
  have h8 (q : Pattern) (ha : d129403 q = 1) (hb : d181732 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129403, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129404 q = 1) (hb : d181733 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129404, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129405 q = 1) (hb : d181734 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129423 q = 1) (hb : d181761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129423, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43102 q ha hb
  have h12 (q : Pattern) (ha : d129424 q = 1) (hb : d181762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129424, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129425 q = 1) (hb : d181763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129425, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129426 q = 1) (hb : d181764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129426, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129427 q = 1) (hb : d181765 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129428 q = 1) (hb : d181766 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro43104 (p : Pattern) (ha : d129434 p = 1) (hb : d181772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129429 q = 1) (hb : d181767 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43103 q ha hb
    | true =>
      simp only [d129429, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129430 q = 1) (hb : d181768 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129431 q = 1) (hb : d181769 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129432 q = 1) (hb : d181770 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129433 q = 1) (hb : d181771 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129434 q = 1) (hb : d181772 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43105 (p : Pattern) (ha : d129440 p = 1) (hb : d181778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129435 q = 1) (hb : d181773 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43104 q ha hb
    | true =>
      simp only [d129435, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129436 q = 1) (hb : d181774 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129437 q = 1) (hb : d181775 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129438 q = 1) (hb : d181776 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129439 q = 1) (hb : d181777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129440 q = 1) (hb : d181778 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43106 (p : Pattern) (ha : d129446 p = 1) (hb : d181784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129441 q = 1) (hb : d181779 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43105 q ha hb
    | true =>
      simp only [d129441, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129442 q = 1) (hb : d181780 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129443 q = 1) (hb : d181781 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129444 q = 1) (hb : d181782 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129445 q = 1) (hb : d181783 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129446 q = 1) (hb : d181784 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43107 (p : Pattern) (ha : d129452 p = 1) (hb : d181790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d181785 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43106 q ha hb
    | true =>
      simp only [d129447, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d181786 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d181787 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d181788 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d181789 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d181790 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43108 (p : Pattern) (ha : d129458 p = 1) (hb : d181796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d181791 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43107 q ha hb
    | true =>
      simp only [d129453, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d181792 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d181793 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d181794 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d181795 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d181796 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43109 (p : Pattern) (ha : d129464 p = 1) (hb : d181802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d181797 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43108 q ha hb
    | true =>
      simp only [d129459, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d181798 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d181799 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d181800 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d181801 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d181802 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43110 (p : Pattern) (ha : d129470 p = 1) (hb : d181808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d181803 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43109 q ha hb
    | true =>
      simp only [d129465, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d181804 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d181805 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d181806 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d181807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d181808 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43111 (p : Pattern) (ha : d18538 p = 1) (hb : d173704 p = 1) : d30 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18534 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18535 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18536 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18537 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18538 q = 1) (hb : d173704 q = 1) : d30 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18538, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18538, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro43112 (p : Pattern) (ha : d18548 p = 1) (hb : d173704 p = 1) : d187879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18539 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18540 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18541 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18542 q = 1) (hb : d173704 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18543 q = 1) (hb : d173704 q = 1) : d35 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18543, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18543, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18547 q = 1) (hb : d173704 q = 1) : d18547 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18548 q = 1) (hb : d173704 q = 1) : d187879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18548, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18548, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43113 (p : Pattern) (ha : d18554 p = 1) (hb : d173704 p = 1) : d187885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18549 q = 1) (hb : d173704 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43112 q ha hb
    | true =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18550 q = 1) (hb : d173704 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18551 q = 1) (hb : d173704 q = 1) : d187882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18551, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18551, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18552 q = 1) (hb : d173704 q = 1) : d187883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18552, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18552, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18553 q = 1) (hb : d173704 q = 1) : d187884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18553, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18553, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18554 q = 1) (hb : d173704 q = 1) : d187885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18554, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18554, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43114 (p : Pattern) (ha : d18560 p = 1) (hb : d173704 p = 1) : d187891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d173704 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43113 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18556 q = 1) (hb : d173704 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18557 q = 1) (hb : d173704 q = 1) : d187888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18557, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18557, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18558 q = 1) (hb : d173704 q = 1) : d187889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18558, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18558, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18559 q = 1) (hb : d173704 q = 1) : d187890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18559, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18559, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18560 q = 1) (hb : d173704 q = 1) : d187891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18560, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18560, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43115 (p : Pattern) (ha : d18566 p = 1) (hb : d173704 p = 1) : d187897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18561 q = 1) (hb : d173704 q = 1) : d187892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18561, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18561, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43114 q ha hb
  have h2 (q : Pattern) (ha : d18562 q = 1) (hb : d173704 q = 1) : d187893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18562, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18562, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18563 q = 1) (hb : d173704 q = 1) : d187894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18563, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18563, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18564 q = 1) (hb : d173704 q = 1) : d187895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18564, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18564, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18565 q = 1) (hb : d173704 q = 1) : d187896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18565, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18565, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18566 q = 1) (hb : d173704 q = 1) : d187897 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18566, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18566, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43116 (p : Pattern) (ha : d18575 p = 1) (hb : d173704 p = 1) : d144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18571 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d140 q = 1) (hb : d131097 q = 1) : d140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18572 q = 1) (hb : d173703 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18572, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18573 q = 1) (hb : d173704 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18573, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18535 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18536 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18574 q = 1) (hb : d173704 q = 1) : d143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18574, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18574, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18537 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18575 q = 1) (hb : d173704 q = 1) : d144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18575, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18575, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43117 (p : Pattern) (ha : d18585 p = 1) (hb : d173704 p = 1) : d187902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18539 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18540 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18541 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18579 q = 1) (hb : d173704 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18542 q = 1) (hb : d173704 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18580 q = 1) (hb : d173704 q = 1) : d149 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18580, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18580, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18584 q = 1) (hb : d173704 q = 1) : d18584 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18585 q = 1) (hb : d173704 q = 1) : d187902 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18585, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18585, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43118 (p : Pattern) (ha : d18591 p = 1) (hb : d173704 p = 1) : d187908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d173704 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43117 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d173704 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18549 q = 1) (hb : d173704 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43112 q ha hb
    | true =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18550 q = 1) (hb : d173704 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18588 q = 1) (hb : d173704 q = 1) : d187905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18588, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18588, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18589 q = 1) (hb : d173704 q = 1) : d187906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18589, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18589, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18590 q = 1) (hb : d173704 q = 1) : d187907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18590, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18590, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18591 q = 1) (hb : d173704 q = 1) : d187908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18591, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18591, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43119 (p : Pattern) (ha : d132592 p = 1) (hb : d173704 p = 1) : d187914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d173704 q = 1) : d187909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43118 q ha hb
    | true =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43113 q ha hb
  have h2 (q : Pattern) (ha : d132588 q = 1) (hb : d173704 q = 1) : d187910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132588, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132588, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18555 q = 1) (hb : d173704 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43113 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18556 q = 1) (hb : d173704 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132589 q = 1) (hb : d173704 q = 1) : d187911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132589, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132589, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132590 q = 1) (hb : d173704 q = 1) : d187912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132590, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132590, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132591 q = 1) (hb : d173704 q = 1) : d187913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132591, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132591, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132592 q = 1) (hb : d173704 q = 1) : d187914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132592, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132592, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43120 (p : Pattern) (ha : d132598 p = 1) (hb : d173704 p = 1) : d187920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132593 q = 1) (hb : d173704 q = 1) : d187915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132593, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132593, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43119 q ha hb
  have h2 (q : Pattern) (ha : d132594 q = 1) (hb : d173704 q = 1) : d187916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132594, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132594, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132595 q = 1) (hb : d173704 q = 1) : d187917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132595, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132595, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132596 q = 1) (hb : d173704 q = 1) : d187918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132596, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132596, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132597 q = 1) (hb : d173704 q = 1) : d187919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132597, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132597, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132598 q = 1) (hb : d173704 q = 1) : d187920 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132598, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132598, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43121 (p : Pattern) (ha : d18695 p = 1) (hb : d173704 p = 1) : d187950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d173704 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43113 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18691 q = 1) (hb : d173704 q = 1) : d187946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18691, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18692 q = 1) (hb : d173704 q = 1) : d187947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18692, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18693 q = 1) (hb : d173704 q = 1) : d187948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18693, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18694 q = 1) (hb : d173704 q = 1) : d187949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18694, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18695 q = 1) (hb : d173704 q = 1) : d187950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18695, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43122 (p : Pattern) (ha : d18639 p = 1) (hb : d173704 p = 1) : d15966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18631 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320 q = 1) (hb : d131097 q = 1) : d320 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18632 q = 1) (hb : d173703 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18632, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18633 q = 1) (hb : d173704 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18633, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18571 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d131097 q = 1) : d140 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18572 q = 1) (hb : d173703 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18572, d173703, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18573 q = 1) (hb : d173704 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18573, d173704, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18634 q = 1) (hb : d173704 q = 1) : d323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18634, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18634, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d18635 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18636 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18637 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d18534 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18535 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18536 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18638 q = 1) (hb : d173704 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18639 q = 1) (hb : d173704 q = 1) : d15966 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18639, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18639, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43123 (p : Pattern) (ha : d18649 p = 1) (hb : d173704 p = 1) : d187926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43122 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18539 q = 1) (hb : d173704 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18540 q = 1) (hb : d173704 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18541 q = 1) (hb : d173704 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18579 q = 1) (hb : d173704 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18644 q = 1) (hb : d173704 q = 1) : d15971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18644, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18644, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18648 q = 1) (hb : d173704 q = 1) : d18648 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18649 q = 1) (hb : d173704 q = 1) : d187926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18649, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18649, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro43124 (p : Pattern) (ha : d18655 p = 1) (hb : d173704 p = 1) : d187932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18650 q = 1) (hb : d173704 q = 1) : d187927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18650, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43123 q ha hb
    | true =>
      simp only [d18650, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18651 q = 1) (hb : d173704 q = 1) : d187928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18651, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18651, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18586 q = 1) (hb : d173704 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43117 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18587 q = 1) (hb : d173704 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18652 q = 1) (hb : d173704 q = 1) : d187929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18652, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18652, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18653 q = 1) (hb : d173704 q = 1) : d187930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18653, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18653, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18654 q = 1) (hb : d173704 q = 1) : d187931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18654, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18654, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18655 q = 1) (hb : d173704 q = 1) : d187932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18655, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18655, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43125 (p : Pattern) (ha : d18683 p = 1) (hb : d173704 p = 1) : d187938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d173704 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43117 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d173704 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18680 q = 1) (hb : d173704 q = 1) : d187935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18680, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18680, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18681 q = 1) (hb : d173704 q = 1) : d187936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18681, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18681, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18682 q = 1) (hb : d173704 q = 1) : d187937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18682, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18682, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18683 q = 1) (hb : d173704 q = 1) : d187938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18683, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18683, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43126 (p : Pattern) (ha : d132608 p = 1) (hb : d173704 p = 1) : d187944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18656 q = 1) (hb : d173704 q = 1) : d187933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18656, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43124 q ha hb
    | true =>
      simp only [d18656, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43118 q ha hb
  have h2 (q : Pattern) (ha : d132604 q = 1) (hb : d173704 q = 1) : d187934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132604, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132604, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18684 q = 1) (hb : d173704 q = 1) : d187939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18684, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43125 q ha hb
    | true =>
      simp only [d18684, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18685 q = 1) (hb : d173704 q = 1) : d187940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18685, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18685, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132605 q = 1) (hb : d173704 q = 1) : d187941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132605, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132605, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132606 q = 1) (hb : d173704 q = 1) : d187942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132606, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132606, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132607 q = 1) (hb : d173704 q = 1) : d187943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132607, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132607, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132608 q = 1) (hb : d173704 q = 1) : d187944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132608, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132608, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43127 (p : Pattern) (ha : d132614 p = 1) (hb : d173704 p = 1) : d187956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132609 q = 1) (hb : d173704 q = 1) : d187945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132609, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132609, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43126 q ha hb
  have h2 (q : Pattern) (ha : d18696 q = 1) (hb : d173704 q = 1) : d187951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43121 q ha hb
  have h3 (q : Pattern) (ha : d132610 q = 1) (hb : d173704 q = 1) : d187952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132610, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132610, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132611 q = 1) (hb : d173704 q = 1) : d187953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132611, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132611, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132612 q = 1) (hb : d173704 q = 1) : d187954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132612, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132612, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132613 q = 1) (hb : d173704 q = 1) : d187955 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132613, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132613, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132614 q = 1) (hb : d173704 q = 1) : d187956 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132614, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132614, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43128 (p : Pattern) (ha : d132620 p = 1) (hb : d173704 p = 1) : d187962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18567 q = 1) (hb : d173704 q = 1) : d187898 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18567, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18567, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43115 q ha hb
  have h2 (q : Pattern) (ha : d18568 q = 1) (hb : d173704 q = 1) : d187899 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18568, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18568, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18569 q = 1) (hb : d173704 q = 1) : d187900 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18569, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18569, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18570 q = 1) (hb : d173704 q = 1) : d187901 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18570, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18570, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132599 q = 1) (hb : d173704 q = 1) : d187921 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132599, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132599, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43120 q ha hb
  have h6 (q : Pattern) (ha : d132600 q = 1) (hb : d173704 q = 1) : d187922 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132600, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132600, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132601 q = 1) (hb : d173704 q = 1) : d187923 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132601, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132601, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132602 q = 1) (hb : d173704 q = 1) : d187924 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132602, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132602, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132603 q = 1) (hb : d173704 q = 1) : d187925 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132603, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132603, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132615 q = 1) (hb : d173704 q = 1) : d187957 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132615, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132615, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43127 q ha hb
  have h11 (q : Pattern) (ha : d132616 q = 1) (hb : d173704 q = 1) : d187958 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132616, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132616, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d132617 q = 1) (hb : d173704 q = 1) : d187959 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132617, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132617, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132618 q = 1) (hb : d173704 q = 1) : d187960 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132618, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132618, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132619 q = 1) (hb : d173704 q = 1) : d187961 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132619, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132619, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132620 q = 1) (hb : d173704 q = 1) : d187962 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132620, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d132620, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43129 (p : Pattern) (ha : d18751 p = 1) (hb : d173704 p = 1) : d187973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18738 q = 1) (hb : d173704 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18749 q = 1) (hb : d173704 q = 1) : d480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18749, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18749, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18750 q = 1) (hb : d173704 q = 1) : d18750 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18751 q = 1) (hb : d173704 q = 1) : d187973 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18751, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18751, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43130 (p : Pattern) (ha : d18811 p = 1) (hb : d173704 p = 1) : d187996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18752 q = 1) (hb : d173704 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43129 q ha hb
    | true =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18753 q = 1) (hb : d173704 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18808 q = 1) (hb : d173704 q = 1) : d187993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18808, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18808, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18809 q = 1) (hb : d173704 q = 1) : d187994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18809, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18809, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18810 q = 1) (hb : d173704 q = 1) : d187995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18810, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18810, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18811 q = 1) (hb : d173704 q = 1) : d187996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18811, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18811, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43131 (p : Pattern) (ha : d18817 p = 1) (hb : d173704 p = 1) : d188002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18812 q = 1) (hb : d173704 q = 1) : d187997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18812, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43130 q ha hb
    | true =>
      simp only [d18812, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18813 q = 1) (hb : d173704 q = 1) : d187998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18813, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18813, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18814 q = 1) (hb : d173704 q = 1) : d187999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18814, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18814, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18815 q = 1) (hb : d173704 q = 1) : d188000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18815, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18815, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18816 q = 1) (hb : d173704 q = 1) : d188001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18816, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18816, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18817 q = 1) (hb : d173704 q = 1) : d188002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18817, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18817, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43132 (p : Pattern) (ha : d18719 p = 1) (hb : d173704 p = 1) : d16077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18708 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d544 q = 1) (hb : d131097 q = 1) : d544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18709 q = 1) (hb : d173703 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18709, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18710 q = 1) (hb : d173704 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18710, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18711 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d131097 q = 1) : d9460 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18712 q = 1) (hb : d173703 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18712, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18713 q = 1) (hb : d173704 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18713, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18714 q = 1) (hb : d173704 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d18715 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18716 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18717 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d18635 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18636 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18637 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18718 q = 1) (hb : d173704 q = 1) : d16076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18718, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18718, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18719 q = 1) (hb : d173704 q = 1) : d16077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18719, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18719, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43133 (p : Pattern) (ha : d18723 p = 1) (hb : d173704 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18635 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9384 q = 1) (hb : d131097 q = 1) : d9384 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18636 q = 1) (hb : d173703 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18636, d173703, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18637 q = 1) (hb : d173704 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18637, d173704, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d131097 q = 1) : d26 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18535 q = 1) (hb : d173703 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18535, d173703, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18536 q = 1) (hb : d173704 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18536, d173704, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18638 q = 1) (hb : d173704 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18537 q = 1) (hb : d173704 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18723 q = 1) (hb : d173704 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18723, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18723, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43134 (p : Pattern) (ha : d18735 p = 1) (hb : d173704 p = 1) : d187963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18720 q = 1) (hb : d173704 q = 1) : d16078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18720, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43132 q ha hb
    | true =>
      simp only [d18720, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43122 q ha hb
  have h2 (q : Pattern) (ha : d18721 q = 1) (hb : d173704 q = 1) : d16079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18721, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18721, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18722 q = 1) (hb : d173704 q = 1) : d16080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18722, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18722, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18724 q = 1) (hb : d173704 q = 1) : d16082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18724, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43122 q ha hb
    | true =>
      simp only [d18724, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43133 q ha hb
  have h5 (q : Pattern) (ha : d18725 q = 1) (hb : d173704 q = 1) : d16083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18725, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18725, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18726 q = 1) (hb : d173704 q = 1) : d16084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18726, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18726, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18727 q = 1) (hb : d173704 q = 1) : d16085 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18727, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18727, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18640 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43122 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
  have h9 (q : Pattern) (ha : d18641 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18642 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18576 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
  have h12 (q : Pattern) (ha : d18577 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18578 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18643 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18728 q = 1) (hb : d173704 q = 1) : d16086 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18728, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18728, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18734 q = 1) (hb : d173704 q = 1) : d18734 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d18735 q = 1) (hb : d173704 q = 1) : d187963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18735, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18735, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro43135 (p : Pattern) (ha : d18742 p = 1) (hb : d173704 p = 1) : d187966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d173704 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43122 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d173704 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d173704 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d173704 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43116 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43111 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d173704 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d173704 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d173704 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18738 q = 1) (hb : d173704 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18739 q = 1) (hb : d173704 q = 1) : d16035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18739, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18739, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18741 q = 1) (hb : d173704 q = 1) : d18741 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18742 q = 1) (hb : d173704 q = 1) : d187966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18742, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18742, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43136 (p : Pattern) (ha : d18748 p = 1) (hb : d173704 p = 1) : d187972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18736 q = 1) (hb : d173704 q = 1) : d187964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18736, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43134 q ha hb
    | true =>
      simp only [d18736, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18737 q = 1) (hb : d173704 q = 1) : d187965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18737, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18737, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18743 q = 1) (hb : d173704 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43135 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18744 q = 1) (hb : d173704 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18745 q = 1) (hb : d173704 q = 1) : d187969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18745, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18745, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18746 q = 1) (hb : d173704 q = 1) : d187970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18746, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18746, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18747 q = 1) (hb : d173704 q = 1) : d187971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18747, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18747, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18748 q = 1) (hb : d173704 q = 1) : d187972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18748, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18748, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43137 (p : Pattern) (ha : d18757 p = 1) (hb : d173704 p = 1) : d187979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d173704 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43135 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d173704 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18752 q = 1) (hb : d173704 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43129 q ha hb
    | true =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18753 q = 1) (hb : d173704 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18754 q = 1) (hb : d173704 q = 1) : d187976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18754, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18754, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18755 q = 1) (hb : d173704 q = 1) : d187977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18755, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18755, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18756 q = 1) (hb : d173704 q = 1) : d187978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18756, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18756, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18757 q = 1) (hb : d173704 q = 1) : d187979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18757, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18757, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43138 (p : Pattern) (ha : d18800 p = 1) (hb : d173704 p = 1) : d187985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d173704 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43135 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d173704 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18797 q = 1) (hb : d173704 q = 1) : d187982 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18797, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18797, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18798 q = 1) (hb : d173704 q = 1) : d187983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18798, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18798, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18799 q = 1) (hb : d173704 q = 1) : d187984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18799, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18799, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18800 q = 1) (hb : d173704 q = 1) : d187985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18800, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18800, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43139 (p : Pattern) (ha : d132625 p = 1) (hb : d173704 p = 1) : d187991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18758 q = 1) (hb : d173704 q = 1) : d187980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18758, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43136 q ha hb
    | true =>
      simp only [d18758, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43137 q ha hb
  have h2 (q : Pattern) (ha : d132621 q = 1) (hb : d173704 q = 1) : d187981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132621, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132621, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18801 q = 1) (hb : d173704 q = 1) : d187986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18801, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43138 q ha hb
    | true =>
      simp only [d18801, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18802 q = 1) (hb : d173704 q = 1) : d187987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18802, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18802, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132622 q = 1) (hb : d173704 q = 1) : d187988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132622, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132622, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132623 q = 1) (hb : d173704 q = 1) : d187989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132623, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132623, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132624 q = 1) (hb : d173704 q = 1) : d187990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132624, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132624, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132625 q = 1) (hb : d173704 q = 1) : d187991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132625, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132625, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43140 (p : Pattern) (ha : d132631 p = 1) (hb : d173704 p = 1) : d188008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132626 q = 1) (hb : d173704 q = 1) : d187992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132626, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132626, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43139 q ha hb
  have h2 (q : Pattern) (ha : d18818 q = 1) (hb : d173704 q = 1) : d188003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18818, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18818, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43131 q ha hb
  have h3 (q : Pattern) (ha : d132627 q = 1) (hb : d173704 q = 1) : d188004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132627, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132627, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132628 q = 1) (hb : d173704 q = 1) : d188005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132628, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132628, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132629 q = 1) (hb : d173704 q = 1) : d188006 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132629, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132629, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132630 q = 1) (hb : d173704 q = 1) : d188007 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132630, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132630, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132631 q = 1) (hb : d173704 q = 1) : d188008 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132631, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132631, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43141 (p : Pattern) (ha : d132637 p = 1) (hb : d173704 p = 1) : d188014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132632 q = 1) (hb : d173704 q = 1) : d188009 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132632, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132632, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43140 q ha hb
  have h2 (q : Pattern) (ha : d132633 q = 1) (hb : d173704 q = 1) : d188010 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132633, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132633, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132634 q = 1) (hb : d173704 q = 1) : d188011 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132634, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132634, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132635 q = 1) (hb : d173704 q = 1) : d188012 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132635, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132635, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132636 q = 1) (hb : d173704 q = 1) : d188013 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132636, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132636, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132637 q = 1) (hb : d173704 q = 1) : d188014 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132637, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132637, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43142 (p : Pattern) (ha : d18858 p = 1) (hb : d173704 p = 1) : d758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18631 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d320 q = 1) (hb : d131097 q = 1) : d320 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18632 q = 1) (hb : d173703 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18632, d173703, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18633 q = 1) (hb : d173704 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18633, d173704, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18843 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18844 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18845 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18857 q = 1) (hb : d173704 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18857, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18857, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18851 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18858 q = 1) (hb : d173704 q = 1) : d758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18858, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18858, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43143 (p : Pattern) (ha : d18862 p = 1) (hb : d173704 p = 1) : d762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18844 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18845 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18851 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18862 q = 1) (hb : d173704 q = 1) : d762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18862, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18862, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro43144 (p : Pattern) (ha : d18895 p = 1) (hb : d173704 p = 1) : d188026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18863 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43142 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43143 q ha hb
  have h2 (q : Pattern) (ha : d18864 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18865 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18882 q = 1) (hb : d173704 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18893 q = 1) (hb : d173704 q = 1) : d772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18893, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18893, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18894 q = 1) (hb : d173704 q = 1) : d18894 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18895 q = 1) (hb : d173704 q = 1) : d188026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18895, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18895, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43145 (p : Pattern) (ha : d18970 p = 1) (hb : d173704 p = 1) : d188049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18896 q = 1) (hb : d173704 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43144 q ha hb
    | true =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18897 q = 1) (hb : d173704 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18967 q = 1) (hb : d173704 q = 1) : d188046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18967, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18967, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18968 q = 1) (hb : d173704 q = 1) : d188047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18968, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18968, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18969 q = 1) (hb : d173704 q = 1) : d188048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18969, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18969, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18970 q = 1) (hb : d173704 q = 1) : d188049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18970, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18970, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43146 (p : Pattern) (ha : d18976 p = 1) (hb : d173704 p = 1) : d188055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18971 q = 1) (hb : d173704 q = 1) : d188050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18971, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43145 q ha hb
    | true =>
      simp only [d18971, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18972 q = 1) (hb : d173704 q = 1) : d188051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18972, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18972, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18973 q = 1) (hb : d173704 q = 1) : d188052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18973, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18973, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18974 q = 1) (hb : d173704 q = 1) : d188053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18974, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18974, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18975 q = 1) (hb : d173704 q = 1) : d188054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18975, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18975, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18976 q = 1) (hb : d173704 q = 1) : d188055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18976, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18976, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43147 (p : Pattern) (ha : d18842 p = 1) (hb : d173704 p = 1) : d16274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18831 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d835 q = 1) (hb : d131097 q = 1) : d835 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18832 q = 1) (hb : d173703 q = 1) : d836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18832, d173703, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18832, d173703, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18833 q = 1) (hb : d173704 q = 1) : d837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18833, d173704, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18833, d173704, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18834 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d131097 q = 1) : d9589 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18835 q = 1) (hb : d173703 q = 1) : d16270 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18835, d173703, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18835, d173703, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18836 q = 1) (hb : d173704 q = 1) : d16271 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18836, d173704, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18836, d173704, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18837 q = 1) (hb : d173704 q = 1) : d16272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18837, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18837, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d18838 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d131097 q = 1) : d9599 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18839 q = 1) (hb : d173703 q = 1) : d14529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18839, d173703, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d18839, d173703, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18840 q = 1) (hb : d173704 q = 1) : d14530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18840, d173704, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18840, d173704, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d18715 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18716 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18717 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18841 q = 1) (hb : d173704 q = 1) : d16273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18841, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18841, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18842 q = 1) (hb : d173704 q = 1) : d16274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18842, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18842, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43148 (p : Pattern) (ha : d18847 p = 1) (hb : d173704 p = 1) : d16227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18708 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d544 q = 1) (hb : d131097 q = 1) : d544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18709 q = 1) (hb : d173703 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18709, d173703, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18710 q = 1) (hb : d173704 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18710, d173704, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18711 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d131097 q = 1) : d9460 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18712 q = 1) (hb : d173703 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18712, d173703, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18713 q = 1) (hb : d173704 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18713, d173704, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18714 q = 1) (hb : d173704 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d18715 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18716 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18717 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d18843 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18844 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18845 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18846 q = 1) (hb : d173704 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18847 q = 1) (hb : d173704 q = 1) : d16227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18847, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18847, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43149 (p : Pattern) (ha : d18852 p = 1) (hb : d173704 p = 1) : d16278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18715 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9470 q = 1) (hb : d131097 q = 1) : d9470 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18716 q = 1) (hb : d173703 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18716, d173703, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18717 q = 1) (hb : d173704 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18717, d173704, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18843 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d131097 q = 1) : d752 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18844 q = 1) (hb : d173703 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18844, d173703, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18845 q = 1) (hb : d173704 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18845, d173704, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18846 q = 1) (hb : d173704 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18851 q = 1) (hb : d173704 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18852 q = 1) (hb : d173704 q = 1) : d16278 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18852, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18852, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43150 (p : Pattern) (ha : d18879 p = 1) (hb : d173704 p = 1) : d188016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18848 q = 1) (hb : d173704 q = 1) : d16275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18848, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43147 q ha hb
    | true =>
      simp only [d18848, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43148 q ha hb
  have h2 (q : Pattern) (ha : d18849 q = 1) (hb : d173704 q = 1) : d16276 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18849, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18849, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18850 q = 1) (hb : d173704 q = 1) : d16277 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18850, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18850, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18853 q = 1) (hb : d173704 q = 1) : d16279 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18853, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43148 q ha hb
    | true =>
      simp only [d18853, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43149 q ha hb
  have h5 (q : Pattern) (ha : d18854 q = 1) (hb : d173704 q = 1) : d16280 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18854, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18854, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18855 q = 1) (hb : d173704 q = 1) : d16281 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18855, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18855, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18856 q = 1) (hb : d173704 q = 1) : d16282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18856, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18856, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18859 q = 1) (hb : d173704 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43148 q ha hb
    | true =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43142 q ha hb
  have h9 (q : Pattern) (ha : d18860 q = 1) (hb : d173704 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18861 q = 1) (hb : d173704 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18863 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43142 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43143 q ha hb
  have h12 (q : Pattern) (ha : d18864 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18865 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18866 q = 1) (hb : d173704 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18867 q = 1) (hb : d173704 q = 1) : d16283 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18867, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18867, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18878 q = 1) (hb : d173704 q = 1) : d18878 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d18879 q = 1) (hb : d173704 q = 1) : d188016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18879, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18879, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro43151 (p : Pattern) (ha : d18886 p = 1) (hb : d173704 p = 1) : d188019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18859 q = 1) (hb : d173704 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43148 q ha hb
    | true =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43142 q ha hb
  have h2 (q : Pattern) (ha : d18860 q = 1) (hb : d173704 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18861 q = 1) (hb : d173704 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18863 q = 1) (hb : d173704 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43142 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43143 q ha hb
  have h5 (q : Pattern) (ha : d18864 q = 1) (hb : d173704 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18865 q = 1) (hb : d173704 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18866 q = 1) (hb : d173704 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18882 q = 1) (hb : d173704 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18883 q = 1) (hb : d173704 q = 1) : d16232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18883, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18883, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18885 q = 1) (hb : d173704 q = 1) : d18885 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18886 q = 1) (hb : d173704 q = 1) : d188019 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18886, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18886, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43152 (p : Pattern) (ha : d18892 p = 1) (hb : d173704 p = 1) : d188025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18880 q = 1) (hb : d173704 q = 1) : d188017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18880, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43150 q ha hb
    | true =>
      simp only [d18880, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18881 q = 1) (hb : d173704 q = 1) : d188018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18881, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18881, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18887 q = 1) (hb : d173704 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43151 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18888 q = 1) (hb : d173704 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18889 q = 1) (hb : d173704 q = 1) : d188022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18889, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18889, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18890 q = 1) (hb : d173704 q = 1) : d188023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18890, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18890, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18891 q = 1) (hb : d173704 q = 1) : d188024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18891, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18891, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18892 q = 1) (hb : d173704 q = 1) : d188025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18892, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18892, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43153 (p : Pattern) (ha : d18901 p = 1) (hb : d173704 p = 1) : d188032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d173704 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43151 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d173704 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18896 q = 1) (hb : d173704 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43144 q ha hb
    | true =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18897 q = 1) (hb : d173704 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18898 q = 1) (hb : d173704 q = 1) : d188029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18898, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18898, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18899 q = 1) (hb : d173704 q = 1) : d188030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18899, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18899, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18900 q = 1) (hb : d173704 q = 1) : d188031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18900, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18900, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18901 q = 1) (hb : d173704 q = 1) : d188032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18901, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18901, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43154 (p : Pattern) (ha : d18959 p = 1) (hb : d173704 p = 1) : d188038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d173704 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43151 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d173704 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18956 q = 1) (hb : d173704 q = 1) : d188035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18956, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18956, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18957 q = 1) (hb : d173704 q = 1) : d188036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18957, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18957, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18958 q = 1) (hb : d173704 q = 1) : d188037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18958, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18958, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18959 q = 1) (hb : d173704 q = 1) : d188038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18959, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18959, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43155 (p : Pattern) (ha : d132643 p = 1) (hb : d173704 p = 1) : d188044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18902 q = 1) (hb : d173704 q = 1) : d188033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18902, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43152 q ha hb
    | true =>
      simp only [d18902, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43153 q ha hb
  have h2 (q : Pattern) (ha : d132639 q = 1) (hb : d173704 q = 1) : d188034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132639, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132639, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18960 q = 1) (hb : d173704 q = 1) : d188039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18960, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43154 q ha hb
    | true =>
      simp only [d18960, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18961 q = 1) (hb : d173704 q = 1) : d188040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18961, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18961, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132640 q = 1) (hb : d173704 q = 1) : d188041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132640, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132640, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132641 q = 1) (hb : d173704 q = 1) : d188042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132641, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132641, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132642 q = 1) (hb : d173704 q = 1) : d188043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132642, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132642, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132643 q = 1) (hb : d173704 q = 1) : d188044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132643, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132643, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43156 (p : Pattern) (ha : d132649 p = 1) (hb : d173704 p = 1) : d188061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132644 q = 1) (hb : d173704 q = 1) : d188045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132644, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132644, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43155 q ha hb
  have h2 (q : Pattern) (ha : d18977 q = 1) (hb : d173704 q = 1) : d188056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18977, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18977, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43146 q ha hb
  have h3 (q : Pattern) (ha : d132645 q = 1) (hb : d173704 q = 1) : d188057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132645, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132645, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132646 q = 1) (hb : d173704 q = 1) : d188058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132646, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132646, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132647 q = 1) (hb : d173704 q = 1) : d188059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132647, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132647, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132648 q = 1) (hb : d173704 q = 1) : d188060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132648, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132648, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132649 q = 1) (hb : d173704 q = 1) : d188061 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132649, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132649, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43157 (p : Pattern) (ha : d132655 p = 1) (hb : d173704 p = 1) : d188067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132650 q = 1) (hb : d173704 q = 1) : d188062 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132650, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132650, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43156 q ha hb
  have h2 (q : Pattern) (ha : d132651 q = 1) (hb : d173704 q = 1) : d188063 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132651, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132651, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132652 q = 1) (hb : d173704 q = 1) : d188064 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132652, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132652, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132653 q = 1) (hb : d173704 q = 1) : d188065 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132653, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132653, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132654 q = 1) (hb : d173704 q = 1) : d188066 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132654, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132654, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132655 q = 1) (hb : d173704 q = 1) : d188067 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132655, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132655, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43158 (p : Pattern) (ha : d19038 p = 1) (hb : d173704 p = 1) : d16443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19031 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1111 q = 1) (hb : d131097 q = 1) : d1111 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19032 q = 1) (hb : d173703 q = 1) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19032, d173703, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19032, d173703, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19033 q = 1) (hb : d173704 q = 1) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19033, d173704, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19033, d173704, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19034 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19035 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19036 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19037 q = 1) (hb : d173704 q = 1) : d1125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19037, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19037, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19013 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19014 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19015 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19025 q = 1) (hb : d173704 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19038 q = 1) (hb : d173704 q = 1) : d16443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19038, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19038, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43159 (p : Pattern) (ha : d19082 p = 1) (hb : d173704 p = 1) : d14778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19035 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19036 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19081 q = 1) (hb : d173704 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19046 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9846 q = 1) (hb : d131097 q = 1) : d9846 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19047 q = 1) (hb : d173703 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19047, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19048 q = 1) (hb : d173704 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19048, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19049 q = 1) (hb : d173704 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19082 q = 1) (hb : d173704 q = 1) : d14778 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19082, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19082, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43160 (p : Pattern) (ha : d19092 p = 1) (hb : d173704 p = 1) : d188080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19083 q = 1) (hb : d173704 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43159 q ha hb
  have h2 (q : Pattern) (ha : d19084 q = 1) (hb : d173704 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19085 q = 1) (hb : d173704 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19086 q = 1) (hb : d173704 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19087 q = 1) (hb : d173704 q = 1) : d16459 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19087, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19087, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19091 q = 1) (hb : d173704 q = 1) : d19091 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19092 q = 1) (hb : d173704 q = 1) : d188080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19092, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19092, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43161 (p : Pattern) (ha : d19201 p = 1) (hb : d173704 p = 1) : d188106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19093 q = 1) (hb : d173704 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43160 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19094 q = 1) (hb : d173704 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19198 q = 1) (hb : d173704 q = 1) : d188103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19198, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19198, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19199 q = 1) (hb : d173704 q = 1) : d188104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19199, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19199, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19200 q = 1) (hb : d173704 q = 1) : d188105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19200, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19200, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19201 q = 1) (hb : d173704 q = 1) : d188106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19201, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19201, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43162 (p : Pattern) (ha : d19207 p = 1) (hb : d173704 p = 1) : d188112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19202 q = 1) (hb : d173704 q = 1) : d188107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19202, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43161 q ha hb
    | true =>
      simp only [d19202, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19203 q = 1) (hb : d173704 q = 1) : d188108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19203, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19203, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19204 q = 1) (hb : d173704 q = 1) : d188109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19204, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19204, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19205 q = 1) (hb : d173704 q = 1) : d188110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19205, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19205, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19206 q = 1) (hb : d173704 q = 1) : d188111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19206, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19206, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19207 q = 1) (hb : d173704 q = 1) : d188112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19207, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19207, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43163 (p : Pattern) (ha : d19005 p = 1) (hb : d173704 p = 1) : d16511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1211 q = 1) (hb : d131097 q = 1) : d1211 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18992 q = 1) (hb : d173703 q = 1) : d1212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18992, d173703, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d18992, d173703, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18993 q = 1) (hb : d173704 q = 1) : d1213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18993, d173704, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18993, d173704, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18994 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9755 q = 1) (hb : d131097 q = 1) : d9755 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18995 q = 1) (hb : d173703 q = 1) : d16507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18995, d173703, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d18995, d173703, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18996 q = 1) (hb : d173704 q = 1) : d16508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18996, d173704, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18996, d173704, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18997 q = 1) (hb : d173704 q = 1) : d16509 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18997, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18997, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d18998 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9765 q = 1) (hb : d131097 q = 1) : d9765 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18999 q = 1) (hb : d173703 q = 1) : d14836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18999, d173703, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d18999, d173703, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19000 q = 1) (hb : d173704 q = 1) : d14837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19000, d173704, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19000, d173704, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d19001 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d131097 q = 1) : d9780 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19002 q = 1) (hb : d173703 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d19002, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19003 q = 1) (hb : d173704 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19003, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19004 q = 1) (hb : d173704 q = 1) : d16510 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19004, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19004, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19005 q = 1) (hb : d173704 q = 1) : d16511 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19005, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19005, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43164 (p : Pattern) (ha : d19017 p = 1) (hb : d173704 p = 1) : d16442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19006 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1101 q = 1) (hb : d131097 q = 1) : d1101 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19007 q = 1) (hb : d173703 q = 1) : d1102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19007, d173703, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19007, d173703, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19008 q = 1) (hb : d173704 q = 1) : d1103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19008, d173704, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19008, d173704, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d131097 q = 1) : d9791 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19010 q = 1) (hb : d173703 q = 1) : d16438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19010, d173703, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19010, d173703, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19011 q = 1) (hb : d173704 q = 1) : d16439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19011, d173704, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19011, d173704, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19012 q = 1) (hb : d173704 q = 1) : d16440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19012, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19012, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19001 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d131097 q = 1) : d9780 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19002 q = 1) (hb : d173703 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19002, d173703, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19003 q = 1) (hb : d173704 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19003, d173704, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d19013 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19014 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19015 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19016 q = 1) (hb : d173704 q = 1) : d16441 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19016, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19016, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19017 q = 1) (hb : d173704 q = 1) : d16442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19017, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19017, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43165 (p : Pattern) (ha : d19026 p = 1) (hb : d173704 p = 1) : d16516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9816 q = 1) (hb : d131097 q = 1) : d9816 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19022 q = 1) (hb : d173703 q = 1) : d13022 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19022, d173703, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19022, d173703, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19023 q = 1) (hb : d173704 q = 1) : d13023 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19023, d173704, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19023, d173704, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19013 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9802 q = 1) (hb : d131097 q = 1) : d9802 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19014 q = 1) (hb : d173703 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19014, d173703, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19015 q = 1) (hb : d173704 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19015, d173704, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19024 q = 1) (hb : d173704 q = 1) : d16515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19024, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19024, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19025 q = 1) (hb : d173704 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19026 q = 1) (hb : d173704 q = 1) : d16516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19026, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19026, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43166 (p : Pattern) (ha : d19050 p = 1) (hb : d173704 p = 1) : d14773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19042 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5019 q = 1) (hb : d131097 q = 1) : d5019 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19043 q = 1) (hb : d173703 q = 1) : d5020 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19043, d173703, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19043, d173703, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19044 q = 1) (hb : d173704 q = 1) : d5021 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19044, d173704, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19044, d173704, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19045 q = 1) (hb : d173704 q = 1) : d5022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19045, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19045, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19046 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9846 q = 1) (hb : d131097 q = 1) : d9846 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19047 q = 1) (hb : d173703 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19047, d173703, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19048 q = 1) (hb : d173704 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19048, d173704, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19049 q = 1) (hb : d173704 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19050 q = 1) (hb : d173704 q = 1) : d14773 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19050, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19050, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43167 (p : Pattern) (ha : d19067 p = 1) (hb : d173704 p = 1) : d188070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19018 q = 1) (hb : d173704 q = 1) : d16512 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19018, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43163 q ha hb
    | true =>
      simp only [d19018, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
  have h2 (q : Pattern) (ha : d19019 q = 1) (hb : d173704 q = 1) : d16513 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19019, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19019, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19020 q = 1) (hb : d173704 q = 1) : d16514 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19020, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19020, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19027 q = 1) (hb : d173704 q = 1) : d16517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19027, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
    | true =>
      simp only [d19027, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43165 q ha hb
  have h5 (q : Pattern) (ha : d19028 q = 1) (hb : d173704 q = 1) : d16518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19028, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19028, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19029 q = 1) (hb : d173704 q = 1) : d16519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19029, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19029, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19030 q = 1) (hb : d173704 q = 1) : d16520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19030, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19030, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19039 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
  have h9 (q : Pattern) (ha : d19040 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19041 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19051 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43166 q ha hb
  have h12 (q : Pattern) (ha : d19052 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19053 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19054 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19055 q = 1) (hb : d173704 q = 1) : d16521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19055, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19055, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19066 q = 1) (hb : d173704 q = 1) : d19066 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19067 q = 1) (hb : d173704 q = 1) : d188070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19067, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19067, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro43168 (p : Pattern) (ha : d19074 p = 1) (hb : d173704 p = 1) : d188073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43166 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19070 q = 1) (hb : d173704 q = 1) : d16525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19070, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19070, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19071 q = 1) (hb : d173704 q = 1) : d16526 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19071, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19071, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19073 q = 1) (hb : d173704 q = 1) : d19073 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19074 q = 1) (hb : d173704 q = 1) : d188073 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19074, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19074, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43169 (p : Pattern) (ha : d19080 p = 1) (hb : d173704 p = 1) : d188079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19068 q = 1) (hb : d173704 q = 1) : d188071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19068, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43167 q ha hb
    | true =>
      simp only [d19068, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19069 q = 1) (hb : d173704 q = 1) : d188072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19069, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19069, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19075 q = 1) (hb : d173704 q = 1) : d188074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43168 q ha hb
    | true =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19076 q = 1) (hb : d173704 q = 1) : d188075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19077 q = 1) (hb : d173704 q = 1) : d188076 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19077, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19077, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19078 q = 1) (hb : d173704 q = 1) : d188077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19078, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19078, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19079 q = 1) (hb : d173704 q = 1) : d188078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19079, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19079, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19080 q = 1) (hb : d173704 q = 1) : d188079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19080, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19080, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43170 (p : Pattern) (ha : d19098 p = 1) (hb : d173704 p = 1) : d188086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19075 q = 1) (hb : d173704 q = 1) : d188074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43168 q ha hb
    | true =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19076 q = 1) (hb : d173704 q = 1) : d188075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d173704 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43160 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d173704 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19095 q = 1) (hb : d173704 q = 1) : d188083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19095, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19095, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19096 q = 1) (hb : d173704 q = 1) : d188084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19096, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19096, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19097 q = 1) (hb : d173704 q = 1) : d188085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19097, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19097, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19098 q = 1) (hb : d173704 q = 1) : d188086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19098, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19098, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43171 (p : Pattern) (ha : d19174 p = 1) (hb : d173704 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1122 q = 1) (hb : d131097 q = 1) : d1122 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19035 q = 1) (hb : d173703 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19035, d173703, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19036 q = 1) (hb : d173704 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19036, d173704, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19081 q = 1) (hb : d173704 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19174 q = 1) (hb : d173704 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19174, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19174, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro43172 (p : Pattern) (ha : d19184 p = 1) (hb : d173704 p = 1) : d188089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43166 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19175 q = 1) (hb : d173704 q = 1) : d16574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19175, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19175, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43171 q ha hb
  have h9 (q : Pattern) (ha : d19176 q = 1) (hb : d173704 q = 1) : d16575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19176, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19176, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19177 q = 1) (hb : d173704 q = 1) : d16576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19177, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19177, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19178 q = 1) (hb : d173704 q = 1) : d16577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19178, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19178, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19179 q = 1) (hb : d173704 q = 1) : d16578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19179, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19179, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19183 q = 1) (hb : d173704 q = 1) : d19183 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19184 q = 1) (hb : d173704 q = 1) : d188089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19184, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19184, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro43173 (p : Pattern) (ha : d19190 p = 1) (hb : d173704 p = 1) : d188095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19185 q = 1) (hb : d173704 q = 1) : d188090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19185, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43172 q ha hb
    | true =>
      simp only [d19185, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19186 q = 1) (hb : d173704 q = 1) : d188091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19186, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19186, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19187 q = 1) (hb : d173704 q = 1) : d188092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19187, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19187, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19188 q = 1) (hb : d173704 q = 1) : d188093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19188, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19188, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19189 q = 1) (hb : d173704 q = 1) : d188094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19189, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19189, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19190 q = 1) (hb : d173704 q = 1) : d188095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19190, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19190, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43174 (p : Pattern) (ha : d132662 p = 1) (hb : d173704 p = 1) : d188101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19099 q = 1) (hb : d173704 q = 1) : d188087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19099, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43169 q ha hb
    | true =>
      simp only [d19099, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43170 q ha hb
  have h2 (q : Pattern) (ha : d132658 q = 1) (hb : d173704 q = 1) : d188088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132658, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132658, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19191 q = 1) (hb : d173704 q = 1) : d188096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19191, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43173 q ha hb
    | true =>
      simp only [d19191, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19192 q = 1) (hb : d173704 q = 1) : d188097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19192, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19192, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132659 q = 1) (hb : d173704 q = 1) : d188098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132659, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132659, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132660 q = 1) (hb : d173704 q = 1) : d188099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132660, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132660, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132661 q = 1) (hb : d173704 q = 1) : d188100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132661, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132661, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132662 q = 1) (hb : d173704 q = 1) : d188101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132662, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132662, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43175 (p : Pattern) (ha : d132668 p = 1) (hb : d173704 p = 1) : d188118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132663 q = 1) (hb : d173704 q = 1) : d188102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132663, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132663, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43174 q ha hb
  have h2 (q : Pattern) (ha : d19208 q = 1) (hb : d173704 q = 1) : d188113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19208, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19208, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43162 q ha hb
  have h3 (q : Pattern) (ha : d132664 q = 1) (hb : d173704 q = 1) : d188114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132664, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132664, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132665 q = 1) (hb : d173704 q = 1) : d188115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132665, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132665, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132666 q = 1) (hb : d173704 q = 1) : d188116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132666, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132666, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132667 q = 1) (hb : d173704 q = 1) : d188117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132667, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132667, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132668 q = 1) (hb : d173704 q = 1) : d188118 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132668, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132668, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43176 (p : Pattern) (ha : d132674 p = 1) (hb : d173704 p = 1) : d188124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132669 q = 1) (hb : d173704 q = 1) : d188119 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132669, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132669, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43175 q ha hb
  have h2 (q : Pattern) (ha : d132670 q = 1) (hb : d173704 q = 1) : d188120 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132670, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132670, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132671 q = 1) (hb : d173704 q = 1) : d188121 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132671, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132671, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132672 q = 1) (hb : d173704 q = 1) : d188122 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132672, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132672, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132673 q = 1) (hb : d173704 q = 1) : d188123 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132673, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132673, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132674 q = 1) (hb : d173704 q = 1) : d188124 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132674, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132674, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43177 (p : Pattern) (ha : d19270 p = 1) (hb : d173704 p = 1) : d16795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19263 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1571 q = 1) (hb : d131097 q = 1) : d1571 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19264 q = 1) (hb : d173703 q = 1) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19264, d173703, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19264, d173703, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19265 q = 1) (hb : d173704 q = 1) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19265, d173704, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19265, d173704, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19266 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d131097 q = 1) : d10117 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19267 q = 1) (hb : d173703 q = 1) : d16792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19267, d173703, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19267, d173703, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19268 q = 1) (hb : d173704 q = 1) : d16793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19268, d173704, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19268, d173704, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19269 q = 1) (hb : d173704 q = 1) : d16794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19269, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19269, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19245 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19246 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19247 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19257 q = 1) (hb : d173704 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19270 q = 1) (hb : d173704 q = 1) : d16795 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19270, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19270, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43178 (p : Pattern) (ha : d19317 p = 1) (hb : d173704 p = 1) : d15171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1583 q = 1) (hb : d131097 q = 1) : d1583 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19314 q = 1) (hb : d173703 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19314, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19315 q = 1) (hb : d173704 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19315, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19316 q = 1) (hb : d173704 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19278 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10137 q = 1) (hb : d131097 q = 1) : d10137 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19279 q = 1) (hb : d173703 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19279, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19280 q = 1) (hb : d173704 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19280, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19281 q = 1) (hb : d173704 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19317 q = 1) (hb : d173704 q = 1) : d15171 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19317, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19317, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43179 (p : Pattern) (ha : d19327 p = 1) (hb : d173704 p = 1) : d188138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19318 q = 1) (hb : d173704 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43178 q ha hb
  have h2 (q : Pattern) (ha : d19319 q = 1) (hb : d173704 q = 1) : d16804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19320 q = 1) (hb : d173704 q = 1) : d16805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19321 q = 1) (hb : d173704 q = 1) : d16806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19322 q = 1) (hb : d173704 q = 1) : d16811 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19322, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19322, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19326 q = 1) (hb : d173704 q = 1) : d19326 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19327 q = 1) (hb : d173704 q = 1) : d188138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19327, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19327, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43180 (p : Pattern) (ha : d19439 p = 1) (hb : d173704 p = 1) : d188164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19328 q = 1) (hb : d173704 q = 1) : d188139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43179 q ha hb
    | true =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19329 q = 1) (hb : d173704 q = 1) : d188140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19436 q = 1) (hb : d173704 q = 1) : d188161 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19436, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19436, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19437 q = 1) (hb : d173704 q = 1) : d188162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19437, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19437, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19438 q = 1) (hb : d173704 q = 1) : d188163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19438, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19438, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19439 q = 1) (hb : d173704 q = 1) : d188164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19439, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19439, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43181 (p : Pattern) (ha : d19445 p = 1) (hb : d173704 p = 1) : d188170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19440 q = 1) (hb : d173704 q = 1) : d188165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19440, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43180 q ha hb
    | true =>
      simp only [d19440, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19441 q = 1) (hb : d173704 q = 1) : d188166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19441, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19441, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19442 q = 1) (hb : d173704 q = 1) : d188167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19442, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19442, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19443 q = 1) (hb : d173704 q = 1) : d188168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19443, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19443, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19444 q = 1) (hb : d173704 q = 1) : d188169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19444, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19444, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19445 q = 1) (hb : d173704 q = 1) : d188170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19445, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19445, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43182 (p : Pattern) (ha : d19237 p = 1) (hb : d173704 p = 1) : d16863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1666 q = 1) (hb : d131097 q = 1) : d1666 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19224 q = 1) (hb : d173703 q = 1) : d1667 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19224, d173703, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19224, d173703, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19225 q = 1) (hb : d173704 q = 1) : d1668 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19225, d173704, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19225, d173704, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19226 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d131097 q = 1) : d10038 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19227 q = 1) (hb : d173703 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19227, d173703, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19227, d173703, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19228 q = 1) (hb : d173704 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19228, d173704, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19228, d173704, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19229 q = 1) (hb : d173704 q = 1) : d16861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19229, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19229, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19230 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10048 q = 1) (hb : d131097 q = 1) : d10048 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19231 q = 1) (hb : d173703 q = 1) : d15229 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19231, d173703, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19231, d173703, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19232 q = 1) (hb : d173704 q = 1) : d15230 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19232, d173704, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19232, d173704, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d19233 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10065 q = 1) (hb : d131097 q = 1) : d10065 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19234 q = 1) (hb : d173703 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d19234, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19235 q = 1) (hb : d173704 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19235, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19236 q = 1) (hb : d173704 q = 1) : d16862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19236, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19236, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19237 q = 1) (hb : d173704 q = 1) : d16863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19237, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19237, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43183 (p : Pattern) (ha : d19249 p = 1) (hb : d173704 p = 1) : d16791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19238 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1556 q = 1) (hb : d131097 q = 1) : d1556 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19239 q = 1) (hb : d173703 q = 1) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19239, d173703, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19239, d173703, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19240 q = 1) (hb : d173704 q = 1) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19240, d173704, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19240, d173704, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19241 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d131097 q = 1) : d10076 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19242 q = 1) (hb : d173703 q = 1) : d16787 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19242, d173703, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19242, d173703, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19243 q = 1) (hb : d173704 q = 1) : d16788 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19243, d173704, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19243, d173704, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19244 q = 1) (hb : d173704 q = 1) : d16789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19244, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19244, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19233 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d131097 q = 1) : d10065 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19234 q = 1) (hb : d173703 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19234, d173703, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19235 q = 1) (hb : d173704 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19235, d173704, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d19245 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19246 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19247 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19248 q = 1) (hb : d173704 q = 1) : d16790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19248, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19248, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19249 q = 1) (hb : d173704 q = 1) : d16791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19249, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19249, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43184 (p : Pattern) (ha : d19258 p = 1) (hb : d173704 p = 1) : d16868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19253 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10101 q = 1) (hb : d131097 q = 1) : d10101 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19254 q = 1) (hb : d173703 q = 1) : d13348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19254, d173703, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19254, d173703, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19255 q = 1) (hb : d173704 q = 1) : d13349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19255, d173704, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19255, d173704, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19245 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10087 q = 1) (hb : d131097 q = 1) : d10087 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19246 q = 1) (hb : d173703 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19246, d173703, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19247 q = 1) (hb : d173704 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19247, d173704, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19256 q = 1) (hb : d173704 q = 1) : d16867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19256, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19256, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19257 q = 1) (hb : d173704 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19258 q = 1) (hb : d173704 q = 1) : d16868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19258, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19258, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43185 (p : Pattern) (ha : d19282 p = 1) (hb : d173704 p = 1) : d15166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19274 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5135 q = 1) (hb : d131097 q = 1) : d5135 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19275 q = 1) (hb : d173703 q = 1) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19275, d173703, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19275, d173703, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19276 q = 1) (hb : d173704 q = 1) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19276, d173704, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19276, d173704, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19277 q = 1) (hb : d173704 q = 1) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19277, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19277, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19278 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10137 q = 1) (hb : d131097 q = 1) : d10137 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19279 q = 1) (hb : d173703 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19279, d173703, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19280 q = 1) (hb : d173704 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19280, d173704, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19281 q = 1) (hb : d173704 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19282 q = 1) (hb : d173704 q = 1) : d15166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19282, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19282, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43186 (p : Pattern) (ha : d19299 p = 1) (hb : d173704 p = 1) : d188128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19250 q = 1) (hb : d173704 q = 1) : d16864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19250, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43182 q ha hb
    | true =>
      simp only [d19250, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
  have h2 (q : Pattern) (ha : d19251 q = 1) (hb : d173704 q = 1) : d16865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19251, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19251, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19252 q = 1) (hb : d173704 q = 1) : d16866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19252, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19252, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19259 q = 1) (hb : d173704 q = 1) : d16869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19259, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
    | true =>
      simp only [d19259, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43184 q ha hb
  have h5 (q : Pattern) (ha : d19260 q = 1) (hb : d173704 q = 1) : d16870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19260, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19260, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19261 q = 1) (hb : d173704 q = 1) : d16871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19261, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19261, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19262 q = 1) (hb : d173704 q = 1) : d16872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19262, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19262, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19271 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
  have h9 (q : Pattern) (ha : d19272 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19273 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19283 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43185 q ha hb
  have h12 (q : Pattern) (ha : d19284 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19285 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19286 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19287 q = 1) (hb : d173704 q = 1) : d16873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19287, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19287, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19298 q = 1) (hb : d173704 q = 1) : d19298 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19299 q = 1) (hb : d173704 q = 1) : d188128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19299, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19299, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro43187 (p : Pattern) (ha : d19306 p = 1) (hb : d173704 p = 1) : d188131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43185 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19302 q = 1) (hb : d173704 q = 1) : d16877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19302, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19302, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19303 q = 1) (hb : d173704 q = 1) : d16878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19303, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19303, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19305 q = 1) (hb : d173704 q = 1) : d19305 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19306 q = 1) (hb : d173704 q = 1) : d188131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19306, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19306, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43188 (p : Pattern) (ha : d19312 p = 1) (hb : d173704 p = 1) : d188137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19300 q = 1) (hb : d173704 q = 1) : d188129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19300, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43186 q ha hb
    | true =>
      simp only [d19300, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19301 q = 1) (hb : d173704 q = 1) : d188130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19301, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19301, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19307 q = 1) (hb : d173704 q = 1) : d188132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43187 q ha hb
    | true =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19308 q = 1) (hb : d173704 q = 1) : d188133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19309 q = 1) (hb : d173704 q = 1) : d188134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19309, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19309, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19310 q = 1) (hb : d173704 q = 1) : d188135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19310, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19310, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19311 q = 1) (hb : d173704 q = 1) : d188136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19311, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19311, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19312 q = 1) (hb : d173704 q = 1) : d188137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19312, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19312, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43189 (p : Pattern) (ha : d19333 p = 1) (hb : d173704 p = 1) : d188144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19307 q = 1) (hb : d173704 q = 1) : d188132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43187 q ha hb
    | true =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19308 q = 1) (hb : d173704 q = 1) : d188133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d173704 q = 1) : d188139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43179 q ha hb
    | true =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d173704 q = 1) : d188140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19330 q = 1) (hb : d173704 q = 1) : d188141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19330, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19330, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19331 q = 1) (hb : d173704 q = 1) : d188142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19331, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19331, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19332 q = 1) (hb : d173704 q = 1) : d188143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19332, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19332, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19333 q = 1) (hb : d173704 q = 1) : d188144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19333, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19333, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43190 (p : Pattern) (ha : d19412 p = 1) (hb : d173704 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1583 q = 1) (hb : d131097 q = 1) : d1583 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19314 q = 1) (hb : d173703 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19314, d173703, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19315 q = 1) (hb : d173704 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19315, d173704, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19316 q = 1) (hb : d173704 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19412 q = 1) (hb : d173704 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19412, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19412, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro43191 (p : Pattern) (ha : d19422 p = 1) (hb : d173704 p = 1) : d188147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43185 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19413 q = 1) (hb : d173704 q = 1) : d16929 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19413, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19413, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43190 q ha hb
  have h9 (q : Pattern) (ha : d19414 q = 1) (hb : d173704 q = 1) : d16930 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19414, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19414, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19415 q = 1) (hb : d173704 q = 1) : d16931 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19415, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19415, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19416 q = 1) (hb : d173704 q = 1) : d16932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19416, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19416, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19417 q = 1) (hb : d173704 q = 1) : d16933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19417, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19417, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19421 q = 1) (hb : d173704 q = 1) : d19421 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19422 q = 1) (hb : d173704 q = 1) : d188147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19422, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19422, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro43192 (p : Pattern) (ha : d19428 p = 1) (hb : d173704 p = 1) : d188153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19423 q = 1) (hb : d173704 q = 1) : d188148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19423, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43191 q ha hb
    | true =>
      simp only [d19423, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19424 q = 1) (hb : d173704 q = 1) : d188149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19424, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19424, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19425 q = 1) (hb : d173704 q = 1) : d188150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19425, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19425, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19426 q = 1) (hb : d173704 q = 1) : d188151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19426, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19426, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19427 q = 1) (hb : d173704 q = 1) : d188152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19427, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19427, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19428 q = 1) (hb : d173704 q = 1) : d188153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19428, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19428, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43193 (p : Pattern) (ha : d132682 p = 1) (hb : d173704 p = 1) : d188159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19334 q = 1) (hb : d173704 q = 1) : d188145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19334, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43188 q ha hb
    | true =>
      simp only [d19334, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43189 q ha hb
  have h2 (q : Pattern) (ha : d132678 q = 1) (hb : d173704 q = 1) : d188146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132678, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132678, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19429 q = 1) (hb : d173704 q = 1) : d188154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19429, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43192 q ha hb
    | true =>
      simp only [d19429, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19430 q = 1) (hb : d173704 q = 1) : d188155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19430, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19430, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132679 q = 1) (hb : d173704 q = 1) : d188156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132679, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132679, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132680 q = 1) (hb : d173704 q = 1) : d188157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132680, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132680, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132681 q = 1) (hb : d173704 q = 1) : d188158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132681, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132681, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132682 q = 1) (hb : d173704 q = 1) : d188159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132682, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132682, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43194 (p : Pattern) (ha : d132688 p = 1) (hb : d173704 p = 1) : d188176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132683 q = 1) (hb : d173704 q = 1) : d188160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132683, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132683, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43193 q ha hb
  have h2 (q : Pattern) (ha : d19446 q = 1) (hb : d173704 q = 1) : d188171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19446, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19446, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43181 q ha hb
  have h3 (q : Pattern) (ha : d132684 q = 1) (hb : d173704 q = 1) : d188172 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132684, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132684, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132685 q = 1) (hb : d173704 q = 1) : d188173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132685, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132685, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132686 q = 1) (hb : d173704 q = 1) : d188174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132686, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132686, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132687 q = 1) (hb : d173704 q = 1) : d188175 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132687, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132687, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132688 q = 1) (hb : d173704 q = 1) : d188176 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132688, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132688, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43195 (p : Pattern) (ha : d132694 p = 1) (hb : d173704 p = 1) : d188182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132689 q = 1) (hb : d173704 q = 1) : d188177 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132689, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132689, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43194 q ha hb
  have h2 (q : Pattern) (ha : d132690 q = 1) (hb : d173704 q = 1) : d188178 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132690, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132690, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132691 q = 1) (hb : d173704 q = 1) : d188179 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132691, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132691, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132692 q = 1) (hb : d173704 q = 1) : d188180 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132692, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132692, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132693 q = 1) (hb : d173704 q = 1) : d188181 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132693, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132693, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132694 q = 1) (hb : d173704 q = 1) : d188182 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132694, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132694, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43196 (p : Pattern) (ha : d19502 p = 1) (hb : d173704 p = 1) : d17161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19495 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2054 q = 1) (hb : d131097 q = 1) : d2054 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19496 q = 1) (hb : d173703 q = 1) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19496, d173703, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19496, d173703, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19497 q = 1) (hb : d173704 q = 1) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19497, d173704, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19497, d173704, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19498 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10393 q = 1) (hb : d131097 q = 1) : d10393 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19499 q = 1) (hb : d173703 q = 1) : d17158 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19499, d173703, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19499, d173703, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19500 q = 1) (hb : d173704 q = 1) : d17159 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19500, d173704, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19500, d173704, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19501 q = 1) (hb : d173704 q = 1) : d17160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19501, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19501, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19481 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19482 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19483 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19489 q = 1) (hb : d173704 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19502 q = 1) (hb : d173704 q = 1) : d17161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19502, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19502, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43197 (p : Pattern) (ha : d19549 p = 1) (hb : d173704 p = 1) : d15563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2066 q = 1) (hb : d131097 q = 1) : d2066 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19546 q = 1) (hb : d173703 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19546, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19547 q = 1) (hb : d173704 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19547, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19548 q = 1) (hb : d173704 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19510 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10414 q = 1) (hb : d131097 q = 1) : d10414 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19511 q = 1) (hb : d173703 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19511, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19512 q = 1) (hb : d173704 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19512, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19513 q = 1) (hb : d173704 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19549 q = 1) (hb : d173704 q = 1) : d15563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19549, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19549, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43198 (p : Pattern) (ha : d19559 p = 1) (hb : d173704 p = 1) : d188197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19550 q = 1) (hb : d173704 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43197 q ha hb
  have h2 (q : Pattern) (ha : d19551 q = 1) (hb : d173704 q = 1) : d17170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19552 q = 1) (hb : d173704 q = 1) : d17171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19553 q = 1) (hb : d173704 q = 1) : d17172 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19554 q = 1) (hb : d173704 q = 1) : d17177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19554, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19554, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19558 q = 1) (hb : d173704 q = 1) : d19558 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19559 q = 1) (hb : d173704 q = 1) : d188197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19559, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19559, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43199 (p : Pattern) (ha : d19671 p = 1) (hb : d173704 p = 1) : d188223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19560 q = 1) (hb : d173704 q = 1) : d188198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43198 q ha hb
    | true =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19561 q = 1) (hb : d173704 q = 1) : d188199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19668 q = 1) (hb : d173704 q = 1) : d188220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19668, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19668, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19669 q = 1) (hb : d173704 q = 1) : d188221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19669, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19669, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19670 q = 1) (hb : d173704 q = 1) : d188222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19670, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19670, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19671 q = 1) (hb : d173704 q = 1) : d188223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19671, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19671, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43200 (p : Pattern) (ha : d19677 p = 1) (hb : d173704 p = 1) : d188229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19672 q = 1) (hb : d173704 q = 1) : d188224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19672, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43199 q ha hb
    | true =>
      simp only [d19672, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19673 q = 1) (hb : d173704 q = 1) : d188225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19673, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19673, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19674 q = 1) (hb : d173704 q = 1) : d188226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19674, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19674, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19675 q = 1) (hb : d173704 q = 1) : d188227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19675, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19675, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19676 q = 1) (hb : d173704 q = 1) : d188228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19676, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19676, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19677 q = 1) (hb : d173704 q = 1) : d188229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19677, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19677, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43201 (p : Pattern) (ha : d19473 p = 1) (hb : d173704 p = 1) : d17229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19462 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2145 q = 1) (hb : d131097 q = 1) : d2145 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19463 q = 1) (hb : d173703 q = 1) : d2146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19463, d173703, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19463, d173703, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19464 q = 1) (hb : d173704 q = 1) : d2147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19464, d173704, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19464, d173704, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19465 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d131097 q = 1) : d10345 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19466 q = 1) (hb : d173703 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19466, d173703, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19466, d173703, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19467 q = 1) (hb : d173704 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19467, d173704, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19467, d173704, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19468 q = 1) (hb : d173704 q = 1) : d17227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19468, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19468, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d19469 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19470 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19471 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d19472 q = 1) (hb : d173704 q = 1) : d17228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19472, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19472, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19473 q = 1) (hb : d173704 q = 1) : d17229 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19473, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19473, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro43202 (p : Pattern) (ha : d19485 p = 1) (hb : d173704 p = 1) : d17157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19474 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2036 q = 1) (hb : d131097 q = 1) : d2036 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19475 q = 1) (hb : d173703 q = 1) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19475, d173703, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19475, d173703, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19476 q = 1) (hb : d173704 q = 1) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19476, d173704, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19476, d173704, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19477 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d131097 q = 1) : d10366 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19478 q = 1) (hb : d173703 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19478, d173703, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19478, d173703, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19479 q = 1) (hb : d173704 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19479, d173704, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19479, d173704, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19480 q = 1) (hb : d173704 q = 1) : d17155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19480, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19480, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19469 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19470 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19471 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d19481 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19482 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19483 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19484 q = 1) (hb : d173704 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19485 q = 1) (hb : d173704 q = 1) : d17157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19485, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19485, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro43203 (p : Pattern) (ha : d19490 p = 1) (hb : d173704 p = 1) : d17233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19469 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10355 q = 1) (hb : d131097 q = 1) : d10355 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19470 q = 1) (hb : d173703 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19470, d173703, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19471 q = 1) (hb : d173704 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19471, d173704, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10373 q = 1) (hb : d131097 q = 1) : d10373 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19482 q = 1) (hb : d173703 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d19482, d173703, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19483 q = 1) (hb : d173704 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19483, d173704, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19484 q = 1) (hb : d173704 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19489 q = 1) (hb : d173704 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19490 q = 1) (hb : d173704 q = 1) : d17233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19490, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19490, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43204 (p : Pattern) (ha : d19514 p = 1) (hb : d173704 p = 1) : d15558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19506 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5248 q = 1) (hb : d131097 q = 1) : d5248 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19507 q = 1) (hb : d173703 q = 1) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19507, d173703, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19507, d173703, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19508 q = 1) (hb : d173704 q = 1) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19508, d173704, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19508, d173704, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19509 q = 1) (hb : d173704 q = 1) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19509, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19509, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d19510 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10414 q = 1) (hb : d131097 q = 1) : d10414 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19511 q = 1) (hb : d173703 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d19511, d173703, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19512 q = 1) (hb : d173704 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19512, d173704, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19513 q = 1) (hb : d173704 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d19514 q = 1) (hb : d173704 q = 1) : d15558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19514, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19514, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43205 (p : Pattern) (ha : d19531 p = 1) (hb : d173704 p = 1) : d188187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19486 q = 1) (hb : d173704 q = 1) : d17230 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19486, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43201 q ha hb
    | true =>
      simp only [d19486, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
  have h2 (q : Pattern) (ha : d19487 q = 1) (hb : d173704 q = 1) : d17231 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19487, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19487, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19488 q = 1) (hb : d173704 q = 1) : d17232 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19488, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19488, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19491 q = 1) (hb : d173704 q = 1) : d17234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19491, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
    | true =>
      simp only [d19491, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43203 q ha hb
  have h5 (q : Pattern) (ha : d19492 q = 1) (hb : d173704 q = 1) : d17235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19492, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19492, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19493 q = 1) (hb : d173704 q = 1) : d17236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19493, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19493, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19494 q = 1) (hb : d173704 q = 1) : d17237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19494, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19494, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19503 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
  have h9 (q : Pattern) (ha : d19504 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19505 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19515 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43204 q ha hb
  have h12 (q : Pattern) (ha : d19516 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19517 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19518 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19519 q = 1) (hb : d173704 q = 1) : d17238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19519, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19519, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19530 q = 1) (hb : d173704 q = 1) : d19530 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19531 q = 1) (hb : d173704 q = 1) : d188187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19531, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19531, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro43206 (p : Pattern) (ha : d19538 p = 1) (hb : d173704 p = 1) : d188190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43204 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19534 q = 1) (hb : d173704 q = 1) : d17242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19534, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19534, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19535 q = 1) (hb : d173704 q = 1) : d17243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19535, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19535, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19537 q = 1) (hb : d173704 q = 1) : d19537 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19538 q = 1) (hb : d173704 q = 1) : d188190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19538, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19538, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43207 (p : Pattern) (ha : d19544 p = 1) (hb : d173704 p = 1) : d188196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19532 q = 1) (hb : d173704 q = 1) : d188188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19532, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43205 q ha hb
    | true =>
      simp only [d19532, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19533 q = 1) (hb : d173704 q = 1) : d188189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19533, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19533, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19539 q = 1) (hb : d173704 q = 1) : d188191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43206 q ha hb
    | true =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19540 q = 1) (hb : d173704 q = 1) : d188192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19541 q = 1) (hb : d173704 q = 1) : d188193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19541, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19541, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19542 q = 1) (hb : d173704 q = 1) : d188194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19542, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19542, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19543 q = 1) (hb : d173704 q = 1) : d188195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19543, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19543, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19544 q = 1) (hb : d173704 q = 1) : d188196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19544, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19544, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43208 (p : Pattern) (ha : d19565 p = 1) (hb : d173704 p = 1) : d188203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19539 q = 1) (hb : d173704 q = 1) : d188191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43206 q ha hb
    | true =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19540 q = 1) (hb : d173704 q = 1) : d188192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d173704 q = 1) : d188198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43198 q ha hb
    | true =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d173704 q = 1) : d188199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19562 q = 1) (hb : d173704 q = 1) : d188200 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19562, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19562, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19563 q = 1) (hb : d173704 q = 1) : d188201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19563, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19563, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19564 q = 1) (hb : d173704 q = 1) : d188202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19564, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19564, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19565 q = 1) (hb : d173704 q = 1) : d188203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19565, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19565, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43209 (p : Pattern) (ha : d19644 p = 1) (hb : d173704 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19545 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2066 q = 1) (hb : d131097 q = 1) : d2066 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19546 q = 1) (hb : d173703 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d19546, d173703, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19547 q = 1) (hb : d173704 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19547, d173704, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19548 q = 1) (hb : d173704 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19644 q = 1) (hb : d173704 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19644, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19644, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro43210 (p : Pattern) (ha : d19654 p = 1) (hb : d173704 p = 1) : d188206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43204 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19645 q = 1) (hb : d173704 q = 1) : d17294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19645, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19645, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43209 q ha hb
  have h9 (q : Pattern) (ha : d19646 q = 1) (hb : d173704 q = 1) : d17295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19646, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19646, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19647 q = 1) (hb : d173704 q = 1) : d17296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19647, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19647, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19648 q = 1) (hb : d173704 q = 1) : d17297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19648, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19648, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19649 q = 1) (hb : d173704 q = 1) : d17298 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19649, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19649, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19653 q = 1) (hb : d173704 q = 1) : d19653 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19654 q = 1) (hb : d173704 q = 1) : d188206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19654, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19654, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro43211 (p : Pattern) (ha : d19660 p = 1) (hb : d173704 p = 1) : d188212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19655 q = 1) (hb : d173704 q = 1) : d188207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19655, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43210 q ha hb
    | true =>
      simp only [d19655, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19656 q = 1) (hb : d173704 q = 1) : d188208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19656, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19656, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19657 q = 1) (hb : d173704 q = 1) : d188209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19657, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19657, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19658 q = 1) (hb : d173704 q = 1) : d188210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19658, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19658, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19659 q = 1) (hb : d173704 q = 1) : d188211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19659, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19659, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19660 q = 1) (hb : d173704 q = 1) : d188212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19660, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19660, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43212 (p : Pattern) (ha : d132703 p = 1) (hb : d173704 p = 1) : d188218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19566 q = 1) (hb : d173704 q = 1) : d188204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19566, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43207 q ha hb
    | true =>
      simp only [d19566, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43208 q ha hb
  have h2 (q : Pattern) (ha : d132699 q = 1) (hb : d173704 q = 1) : d188205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132699, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132699, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19661 q = 1) (hb : d173704 q = 1) : d188213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19661, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43211 q ha hb
    | true =>
      simp only [d19661, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19662 q = 1) (hb : d173704 q = 1) : d188214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19662, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19662, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132700 q = 1) (hb : d173704 q = 1) : d188215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132700, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132700, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132701 q = 1) (hb : d173704 q = 1) : d188216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132701, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132701, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132702 q = 1) (hb : d173704 q = 1) : d188217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132702, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132702, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132703 q = 1) (hb : d173704 q = 1) : d188218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132703, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132703, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43213 (p : Pattern) (ha : d132709 p = 1) (hb : d173704 p = 1) : d188235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132704 q = 1) (hb : d173704 q = 1) : d188219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132704, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132704, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43212 q ha hb
  have h2 (q : Pattern) (ha : d19678 q = 1) (hb : d173704 q = 1) : d188230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19678, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19678, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43200 q ha hb
  have h3 (q : Pattern) (ha : d132705 q = 1) (hb : d173704 q = 1) : d188231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132705, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132705, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132706 q = 1) (hb : d173704 q = 1) : d188232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132706, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132706, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132707 q = 1) (hb : d173704 q = 1) : d188233 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132707, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132707, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132708 q = 1) (hb : d173704 q = 1) : d188234 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132708, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132708, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132709 q = 1) (hb : d173704 q = 1) : d188235 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132709, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132709, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43214 (p : Pattern) (ha : d132715 p = 1) (hb : d173704 p = 1) : d188241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132710 q = 1) (hb : d173704 q = 1) : d188236 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132710, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132710, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43213 q ha hb
  have h2 (q : Pattern) (ha : d132711 q = 1) (hb : d173704 q = 1) : d188237 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132711, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132711, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132712 q = 1) (hb : d173704 q = 1) : d188238 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132712, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132712, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132713 q = 1) (hb : d173704 q = 1) : d188239 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132713, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132713, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132714 q = 1) (hb : d173704 q = 1) : d188240 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132714, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132714, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132715 q = 1) (hb : d173704 q = 1) : d188241 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132715, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132715, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43215 (p : Pattern) (ha : d132721 p = 1) (hb : d173704 p = 1) : d188247 p = 1 := by
  have h0 (q : Pattern) (ha : d132638 q = 1) (hb : d173704 q = 1) : d188015 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132638, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43128 q ha hb
    | true =>
      simp only [d132638, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43141 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132656 q = 1) (hb : d173704 q = 1) : d188068 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132656, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132656, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43157 q ha hb
  have h3 (q : Pattern) (ha : d132657 q = 1) (hb : d173704 q = 1) : d188069 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132657, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132657, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132675 q = 1) (hb : d173704 q = 1) : d188125 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132675, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132675, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43176 q ha hb
  have h5 (q : Pattern) (ha : d132676 q = 1) (hb : d173704 q = 1) : d188126 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132676, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132676, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132677 q = 1) (hb : d173704 q = 1) : d188127 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132677, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132677, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132695 q = 1) (hb : d173704 q = 1) : d188183 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132695, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132695, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43195 q ha hb
  have h8 (q : Pattern) (ha : d132696 q = 1) (hb : d173704 q = 1) : d188184 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132696, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132696, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132697 q = 1) (hb : d173704 q = 1) : d188185 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132697, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132697, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132698 q = 1) (hb : d173704 q = 1) : d188186 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132698, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132698, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132716 q = 1) (hb : d173704 q = 1) : d188242 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132716, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132716, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43214 q ha hb
  have h12 (q : Pattern) (ha : d132717 q = 1) (hb : d173704 q = 1) : d188243 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132717, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132717, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132718 q = 1) (hb : d173704 q = 1) : d188244 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132718, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132718, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132719 q = 1) (hb : d173704 q = 1) : d188245 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132719, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132719, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132720 q = 1) (hb : d173704 q = 1) : d188246 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132720, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132720, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d132721 q = 1) (hb : d173704 q = 1) : d188247 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132721, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132721, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro43216 (p : Pattern) (ha : d132727 p = 1) (hb : d173704 p = 1) : d188253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132722 q = 1) (hb : d173704 q = 1) : d188248 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132722, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43215 q ha hb
    | true =>
      simp only [d132722, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132723 q = 1) (hb : d173704 q = 1) : d188249 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132723, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132723, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132724 q = 1) (hb : d173704 q = 1) : d188250 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132724, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132724, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132725 q = 1) (hb : d173704 q = 1) : d188251 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132725, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132725, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132726 q = 1) (hb : d173704 q = 1) : d188252 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132726, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132726, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132727 q = 1) (hb : d173704 q = 1) : d188253 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132727, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132727, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43217 (p : Pattern) (ha : d132733 p = 1) (hb : d173704 p = 1) : d188259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132728 q = 1) (hb : d173704 q = 1) : d188254 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132728, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43216 q ha hb
    | true =>
      simp only [d132728, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132729 q = 1) (hb : d173704 q = 1) : d188255 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132729, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132729, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132730 q = 1) (hb : d173704 q = 1) : d188256 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132730, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132730, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132731 q = 1) (hb : d173704 q = 1) : d188257 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132731, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132731, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132732 q = 1) (hb : d173704 q = 1) : d188258 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132732, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132732, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132733 q = 1) (hb : d173704 q = 1) : d188259 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132733, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132733, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43218 (p : Pattern) (ha : d132739 p = 1) (hb : d173704 p = 1) : d188265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132734 q = 1) (hb : d173704 q = 1) : d188260 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132734, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43217 q ha hb
    | true =>
      simp only [d132734, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132735 q = 1) (hb : d173704 q = 1) : d188261 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132735, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132735, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132736 q = 1) (hb : d173704 q = 1) : d188262 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132736, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132736, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132737 q = 1) (hb : d173704 q = 1) : d188263 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132737, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132737, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132738 q = 1) (hb : d173704 q = 1) : d188264 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132738, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132738, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132739 q = 1) (hb : d173704 q = 1) : d188265 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132739, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132739, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43219 (p : Pattern) (ha : d132745 p = 1) (hb : d173704 p = 1) : d188271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132740 q = 1) (hb : d173704 q = 1) : d188266 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132740, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43218 q ha hb
    | true =>
      simp only [d132740, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132741 q = 1) (hb : d173704 q = 1) : d188267 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132741, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132741, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132742 q = 1) (hb : d173704 q = 1) : d188268 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132742, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132742, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132743 q = 1) (hb : d173704 q = 1) : d188269 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132743, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132743, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132744 q = 1) (hb : d173704 q = 1) : d188270 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132744, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132744, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132745 q = 1) (hb : d173704 q = 1) : d188271 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132745, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132745, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43220 (p : Pattern) (ha : d132751 p = 1) (hb : d173704 p = 1) : d188277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132746 q = 1) (hb : d173704 q = 1) : d188272 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132746, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43219 q ha hb
    | true =>
      simp only [d132746, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132747 q = 1) (hb : d173704 q = 1) : d188273 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132747, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132747, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132748 q = 1) (hb : d173704 q = 1) : d188274 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132748, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132748, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132749 q = 1) (hb : d173704 q = 1) : d188275 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132749, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132749, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132750 q = 1) (hb : d173704 q = 1) : d188276 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132750, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132750, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132751 q = 1) (hb : d173704 q = 1) : d188277 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132751, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132751, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43221 (p : Pattern) (ha : d132757 p = 1) (hb : d173704 p = 1) : d188283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132752 q = 1) (hb : d173704 q = 1) : d188278 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132752, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43220 q ha hb
    | true =>
      simp only [d132752, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132753 q = 1) (hb : d173704 q = 1) : d188279 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132753, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132753, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132754 q = 1) (hb : d173704 q = 1) : d188280 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132754, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132754, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132755 q = 1) (hb : d173704 q = 1) : d188281 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132755, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132755, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132756 q = 1) (hb : d173704 q = 1) : d188282 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132756, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132756, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132757 q = 1) (hb : d173704 q = 1) : d188283 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132757, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132757, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43222 (p : Pattern) (ha : d132763 p = 1) (hb : d173704 p = 1) : d188289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132758 q = 1) (hb : d173704 q = 1) : d188284 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132758, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43221 q ha hb
    | true =>
      simp only [d132758, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132759 q = 1) (hb : d173704 q = 1) : d188285 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132759, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132759, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132760 q = 1) (hb : d173704 q = 1) : d188286 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132760, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132760, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132761 q = 1) (hb : d173704 q = 1) : d188287 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132761, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132761, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132762 q = 1) (hb : d173704 q = 1) : d188288 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132762, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132762, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132763 q = 1) (hb : d173704 q = 1) : d188289 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132763, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132763, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43223 (p : Pattern) (ha : d1 p = 1) (hb : d188289 p = 1) : d188289 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d188289 q = 1) : d188289 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro43224 (p : Pattern) (ha : d173704 p = 1) (hb : d187684 p = 1) : d188294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18696 q = 1) (hb : d173704 q = 1) : d187951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43121 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187680 q = 1) : d188290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187680, d188290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187680, d188290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187681 q = 1) : d188291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187681, d188291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187681, d188291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187682 q = 1) : d188292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187682, d188292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187682, d188292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187683 q = 1) : d188293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187683, d188293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187683, d188293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187684 q = 1) : d188294 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187684, d188294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187684, d188294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43225 (p : Pattern) (ha : d173704 p = 1) (hb : d187694 p = 1) : d188304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d173704 q = 1) : d187909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43118 q ha hb
    | true =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43113 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187690 q = 1) : d188300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187690, d188300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187690, d188300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187691 q = 1) : d188301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187691, d188301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187691, d188301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187692 q = 1) : d188302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187692, d188302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187692, d188302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187693 q = 1) : d188303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187693, d188303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187693, d188303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187694 q = 1) : d188304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187694, d188304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187694, d188304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43226 (p : Pattern) (ha : d173704 p = 1) (hb : d187700 p = 1) : d188310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187695 q = 1) : d188305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187695, d188305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187695, d188305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43225 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187696 q = 1) : d188306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187696, d188306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187696, d188306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187697 q = 1) : d188307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187697, d188307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187697, d188307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187698 q = 1) : d188308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187698, d188308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187698, d188308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187699 q = 1) : d188309 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187699, d188309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187699, d188309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187700 q = 1) : d188310 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187700, d188310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187700, d188310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43227 (p : Pattern) (ha : d173704 p = 1) (hb : d187706 p = 1) : d188316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187685 q = 1) : d188295 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187685, d188295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187685, d188295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43224 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187686 q = 1) : d188296 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187686, d188296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187686, d188296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187687 q = 1) : d188297 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187687, d188297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187687, d188297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187688 q = 1) : d188298 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187688, d188298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187688, d188298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187689 q = 1) : d188299 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187689, d188299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187689, d188299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187701 q = 1) : d188311 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187701, d188311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187701, d188311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43226 q ha hb
  have h7 (q : Pattern) (ha : d173704 q = 1) (hb : d187702 q = 1) : d188312 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187702, d188312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187702, d188312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d173704 q = 1) (hb : d187703 q = 1) : d188313 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187703, d188313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187703, d188313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d173704 q = 1) (hb : d187704 q = 1) : d188314 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187704, d188314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187704, d188314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d173704 q = 1) (hb : d187705 q = 1) : d188315 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187705, d188315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187705, d188315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d173704 q = 1) (hb : d187706 q = 1) : d188316 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187706, d188316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187706, d188316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43228 (p : Pattern) (ha : d173704 p = 1) (hb : d187712 p = 1) : d188322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187707 q = 1) : d188317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187707, d188317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43137 q hb ha
    | true =>
      simp only [d187707, d188317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43130 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187708 q = 1) : d188318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187708, d188318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187708, d188318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187709 q = 1) : d188319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187709, d188319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187709, d188319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187710 q = 1) : d188320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187710, d188320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187710, d188320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187711 q = 1) : d188321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187711, d188321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187711, d188321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187712 q = 1) : d188322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187712, d188322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187712, d188322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43229 (p : Pattern) (ha : d173704 p = 1) (hb : d187718 p = 1) : d188328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187713 q = 1) : d188323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187713, d188323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187713, d188323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43228 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187714 q = 1) : d188324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187714, d188324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187714, d188324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187715 q = 1) : d188325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187715, d188325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187715, d188325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187716 q = 1) : d188326 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187716, d188326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187716, d188326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187717 q = 1) : d188327 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187717, d188327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187717, d188327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187718 q = 1) : d188328 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187718, d188328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187718, d188328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43230 (p : Pattern) (ha : d173704 p = 1) (hb : d187724 p = 1) : d188334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187719 q = 1) : d188329 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187719, d188329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187719, d188329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43229 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187720 q = 1) : d188330 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187720, d188330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187720, d188330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187721 q = 1) : d188331 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187721, d188331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187721, d188331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187722 q = 1) : d188332 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187722, d188332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187722, d188332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187723 q = 1) : d188333 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187723, d188333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187723, d188333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187724 q = 1) : d188334 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187724, d188334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187724, d188334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43231 (p : Pattern) (ha : d173704 p = 1) (hb : d187731 p = 1) : d188341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187726 q = 1) : d188336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187726, d188336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43153 q hb ha
    | true =>
      simp only [d187726, d188336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43145 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187727 q = 1) : d188337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187727, d188337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187727, d188337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187728 q = 1) : d188338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187728, d188338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187728, d188338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187729 q = 1) : d188339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187729, d188339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187729, d188339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187730 q = 1) : d188340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187730, d188340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187730, d188340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187731 q = 1) : d188341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187731, d188341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187731, d188341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43232 (p : Pattern) (ha : d173704 p = 1) (hb : d187737 p = 1) : d188347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187732 q = 1) : d188342 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187732, d188342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187732, d188342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43231 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187733 q = 1) : d188343 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187733, d188343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187733, d188343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187734 q = 1) : d188344 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187734, d188344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187734, d188344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187735 q = 1) : d188345 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187735, d188345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187735, d188345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187736 q = 1) : d188346 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187736, d188346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187736, d188346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187737 q = 1) : d188347 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187737, d188347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187737, d188347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43233 (p : Pattern) (ha : d173704 p = 1) (hb : d187743 p = 1) : d188353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187738 q = 1) : d188348 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187738, d188348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187738, d188348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43232 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187739 q = 1) : d188349 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187739, d188349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187739, d188349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187740 q = 1) : d188350 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187740, d188350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187740, d188350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187741 q = 1) : d188351 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187741, d188351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187741, d188351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187742 q = 1) : d188352 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187742, d188352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187742, d188352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187743 q = 1) : d188353 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187743, d188353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187743, d188353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43234 (p : Pattern) (ha : d173704 p = 1) (hb : d187747 p = 1) : d188356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d173704 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43164 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d173704 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d173704 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d173704 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43166 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d173704 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d173704 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d173704 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19083 q = 1) (hb : d173704 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43158 q ha hb
    | true =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43159 q ha hb
  have h9 (q : Pattern) (ha : d19084 q = 1) (hb : d173704 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19085 q = 1) (hb : d173704 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19086 q = 1) (hb : d173704 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173704 q = 1) (hb : d187746 q = 1) : d16455 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187746, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187746, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d132455 q = 1) (hb : d173704 q = 1) : d132455 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d173704 q = 1) (hb : d187747 q = 1) : d188356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187747, d188356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187747, d188356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro43235 (p : Pattern) (ha : d173704 p = 1) (hb : d187753 p = 1) : d188362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187748 q = 1) : d188357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187748, d188357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43234 q ha hb
    | true =>
      simp only [d187748, d188357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187749 q = 1) : d188358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187749, d188358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187749, d188358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d173704 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43160 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d173704 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187750 q = 1) : d188359 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187750, d188359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187750, d188359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187751 q = 1) : d188360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187751, d188360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187751, d188360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d173704 q = 1) (hb : d187752 q = 1) : d188361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187752, d188361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187752, d188361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d173704 q = 1) (hb : d187753 q = 1) : d188362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187753, d188362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187753, d188362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43236 (p : Pattern) (ha : d173704 p = 1) (hb : d187759 p = 1) : d188368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187754 q = 1) : d188363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187754, d188363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43235 q ha hb
    | true =>
      simp only [d187754, d188363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43161 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187755 q = 1) : d188364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187755, d188364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187755, d188364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187756 q = 1) : d188365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187756, d188365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187756, d188365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187757 q = 1) : d188366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187757, d188366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187757, d188366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187758 q = 1) : d188367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187758, d188367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187758, d188367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187759 q = 1) : d188368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187759, d188368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187759, d188368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43237 (p : Pattern) (ha : d173704 p = 1) (hb : d187765 p = 1) : d188374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187760 q = 1) : d188369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187760, d188369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187760, d188369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43236 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187761 q = 1) : d188370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187761, d188370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187761, d188370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187762 q = 1) : d188371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187762, d188371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187762, d188371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187763 q = 1) : d188372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187763, d188372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187763, d188372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187764 q = 1) : d188373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187764, d188373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187764, d188373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187765 q = 1) : d188374 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187765, d188374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187765, d188374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43238 (p : Pattern) (ha : d173704 p = 1) (hb : d187771 p = 1) : d188380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187766 q = 1) : d188375 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187766, d188375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187766, d188375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43237 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187767 q = 1) : d188376 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187767, d188376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187767, d188376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187768 q = 1) : d188377 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187768, d188377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187768, d188377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187769 q = 1) : d188378 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187769, d188378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187769, d188378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187770 q = 1) : d188379 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187770, d188379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187770, d188379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187771 q = 1) : d188380 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187771, d188380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187771, d188380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43239 (p : Pattern) (ha : d173704 p = 1) (hb : d187776 p = 1) : d188384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d173704 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43183 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d173704 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d173704 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d173704 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43185 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d173704 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d173704 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d173704 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19318 q = 1) (hb : d173704 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43177 q ha hb
    | true =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43178 q ha hb
  have h9 (q : Pattern) (ha : d19319 q = 1) (hb : d173704 q = 1) : d16804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19320 q = 1) (hb : d173704 q = 1) : d16805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19321 q = 1) (hb : d173704 q = 1) : d16806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173704 q = 1) (hb : d187775 q = 1) : d16807 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187775, d16807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187775, d16807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d132484 q = 1) (hb : d173704 q = 1) : d132484 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d173704 q = 1) (hb : d187776 q = 1) : d188384 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187776, d188384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187776, d188384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro43240 (p : Pattern) (ha : d173704 p = 1) (hb : d187782 p = 1) : d188390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187777 q = 1) : d188385 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187777, d188385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43239 q ha hb
    | true =>
      simp only [d187777, d188385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187778 q = 1) : d188386 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187778, d188386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187778, d188386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d173704 q = 1) : d188139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43179 q ha hb
    | true =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d173704 q = 1) : d188140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187779 q = 1) : d188387 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187779, d188387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187779, d188387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187780 q = 1) : d188388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187780, d188388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187780, d188388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d173704 q = 1) (hb : d187781 q = 1) : d188389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187781, d188389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187781, d188389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d173704 q = 1) (hb : d187782 q = 1) : d188390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187782, d188390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187782, d188390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43241 (p : Pattern) (ha : d173704 p = 1) (hb : d187788 p = 1) : d188396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187783 q = 1) : d188391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187783, d188391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43240 q ha hb
    | true =>
      simp only [d187783, d188391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43180 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187784 q = 1) : d188392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187784, d188392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187784, d188392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187785 q = 1) : d188393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187785, d188393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187785, d188393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187786 q = 1) : d188394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187786, d188394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187786, d188394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187787 q = 1) : d188395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187787, d188395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187787, d188395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187788 q = 1) : d188396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187788, d188396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187788, d188396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43242 (p : Pattern) (ha : d173704 p = 1) (hb : d187794 p = 1) : d188402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187789 q = 1) : d188397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187789, d188397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187789, d188397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43241 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187790 q = 1) : d188398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187790, d188398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187790, d188398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187791 q = 1) : d188399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187791, d188399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187791, d188399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187792 q = 1) : d188400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187792, d188400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187792, d188400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187793 q = 1) : d188401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187793, d188401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187793, d188401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187794 q = 1) : d188402 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187794, d188402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187794, d188402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43243 (p : Pattern) (ha : d173704 p = 1) (hb : d187800 p = 1) : d188408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187795 q = 1) : d188403 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187795, d188403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187795, d188403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43242 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187796 q = 1) : d188404 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187796, d188404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187796, d188404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187797 q = 1) : d188405 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187797, d188405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187797, d188405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187798 q = 1) : d188406 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187798, d188406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187798, d188406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187799 q = 1) : d188407 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187799, d188407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187799, d188407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187800 q = 1) : d188408 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187800, d188408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187800, d188408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43244 (p : Pattern) (ha : d173704 p = 1) (hb : d187806 p = 1) : d188413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d173704 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43202 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d173704 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d173704 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d173704 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43204 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d173704 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d173704 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d173704 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19550 q = 1) (hb : d173704 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43196 q ha hb
    | true =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43197 q ha hb
  have h9 (q : Pattern) (ha : d19551 q = 1) (hb : d173704 q = 1) : d17170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19552 q = 1) (hb : d173704 q = 1) : d17171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19553 q = 1) (hb : d173704 q = 1) : d17172 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173704 q = 1) (hb : d187805 q = 1) : d17173 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187805, d17173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187805, d17173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d132514 q = 1) (hb : d173704 q = 1) : d132514 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d173704 q = 1) (hb : d187806 q = 1) : d188413 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187806, d188413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187806, d188413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro43245 (p : Pattern) (ha : d173704 p = 1) (hb : d187812 p = 1) : d188419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187807 q = 1) : d188414 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187807, d188414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43244 q ha hb
    | true =>
      simp only [d187807, d188414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187808 q = 1) : d188415 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187808, d188415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187808, d188415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d173704 q = 1) : d188198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43198 q ha hb
    | true =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d173704 q = 1) : d188199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187809 q = 1) : d188416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187809, d188416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187809, d188416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187810 q = 1) : d188417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187810, d188417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187810, d188417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d173704 q = 1) (hb : d187811 q = 1) : d188418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187811, d188418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187811, d188418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d173704 q = 1) (hb : d187812 q = 1) : d188419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187812, d188419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187812, d188419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43246 (p : Pattern) (ha : d173704 p = 1) (hb : d187818 p = 1) : d188425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187813 q = 1) : d188420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187813, d188420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43245 q ha hb
    | true =>
      simp only [d187813, d188420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43199 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187814 q = 1) : d188421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187814, d188421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187814, d188421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187815 q = 1) : d188422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187815, d188422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187815, d188422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187816 q = 1) : d188423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187816, d188423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187816, d188423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187817 q = 1) : d188424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187817, d188424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187817, d188424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187818 q = 1) : d188425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187818, d188425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187818, d188425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43247 (p : Pattern) (ha : d173704 p = 1) (hb : d187824 p = 1) : d188431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187819 q = 1) : d188426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187819, d188426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187819, d188426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43246 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187820 q = 1) : d188427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187820, d188427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187820, d188427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187821 q = 1) : d188428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187821, d188428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187821, d188428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187822 q = 1) : d188429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187822, d188429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187822, d188429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187823 q = 1) : d188430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187823, d188430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187823, d188430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187824 q = 1) : d188431 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187824, d188431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187824, d188431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43248 (p : Pattern) (ha : d173704 p = 1) (hb : d187830 p = 1) : d188437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187825 q = 1) : d188432 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187825, d188432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187825, d188432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43247 q ha hb
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187826 q = 1) : d188433 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187826, d188433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187826, d188433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187827 q = 1) : d188434 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187827, d188434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187827, d188434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187828 q = 1) : d188435 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187828, d188435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187828, d188435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187829 q = 1) : d188436 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187829, d188436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187829, d188436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187830 q = 1) : d188437 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187830, d188437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187830, d188437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43249 (p : Pattern) (ha : d173704 p = 1) (hb : d187836 p = 1) : d188443 p = 1 := by
  have h0 (q : Pattern) (ha : d173704 q = 1) (hb : d187725 q = 1) : d188335 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187725, d188335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43227 q ha hb
    | true =>
      simp only [d187725, d188335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43230 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187744 q = 1) : d188354 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187744, d188354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187744, d188354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43233 q ha hb
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187745 q = 1) : d188355 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187745, d188355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187745, d188355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187772 q = 1) : d188381 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187772, d188381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187772, d188381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43238 q ha hb
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187773 q = 1) : d188382 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187773, d188382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187773, d188382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187774 q = 1) : d188383 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187774, d188383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187774, d188383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d173704 q = 1) (hb : d187801 q = 1) : d188409 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187801, d188409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187801, d188409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43243 q ha hb
  have h8 (q : Pattern) (ha : d173704 q = 1) (hb : d187802 q = 1) : d188410 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187802, d188410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187802, d188410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d173704 q = 1) (hb : d187803 q = 1) : d188411 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187803, d188411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187803, d188411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d173704 q = 1) (hb : d187804 q = 1) : d188412 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187804, d188412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187804, d188412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d173704 q = 1) (hb : d187831 q = 1) : d188438 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187831, d188438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187831, d188438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43248 q ha hb
  have h12 (q : Pattern) (ha : d173704 q = 1) (hb : d187832 q = 1) : d188439 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187832, d188439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187832, d188439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173704 q = 1) (hb : d187833 q = 1) : d188440 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187833, d188440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187833, d188440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d173704 q = 1) (hb : d187834 q = 1) : d188441 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187834, d188441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187834, d188441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d173704 q = 1) (hb : d187835 q = 1) : d188442 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d187835, d188442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d187835, d188442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d173704 q = 1) (hb : d187836 q = 1) : d188443 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d187836, d188443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d187836, d188443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
end NetHack.Soko22Hazard87
