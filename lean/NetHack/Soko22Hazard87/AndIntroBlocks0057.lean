import NetHack.Soko22Hazard87.AndIntroBlocks0056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro14250 (p : Pattern) (ha : d8108 p = 1) (hb : d84426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d84395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d84396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8108 q = 1) (hb : d84426 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d84426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8108, d84426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14251 (p : Pattern) (ha : d84430 p = 1) (hb : d99104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d84403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10105 q ha hb
    | true =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d84404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d99094 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84405, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d99095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d99096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84430 q = 1) (hb : d99104 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84430, d99104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84430, d99104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14252 (p : Pattern) (ha : d84439 p = 1) (hb : d99110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d84391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14244 q ha hb
    | true =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d84392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d84393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d84398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14245 q ha hb
    | true =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d84399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d99098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14247 q ha hb
    | true =>
      simp only [d84409, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d99099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8097 q = 1) (hb : d84415 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10102 q ha hb
    | true =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d99100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d99101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84418, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d99102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84419, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8104 q = 1) (hb : d84422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d84422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14249 q ha hb
    | true =>
      simp only [d8104, d84422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h17 (q : Pattern) (ha : d8105 q = 1) (hb : d84423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d84423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d84423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8106 q = 1) (hb : d84424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d84424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d8106, d84424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d8107 q = 1) (hb : d84425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d84425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d84425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d8109 q = 1) (hb : d84427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d84427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14250 q ha hb
    | true =>
      simp only [d8109, d84427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h21 (q : Pattern) (ha : d8110 q = 1) (hb : d84428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d84428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d84428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8111 q = 1) (hb : d84429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d84429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8111, d84429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d84431 q = 1) (hb : d99105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14251 q ha hb
    | true =>
      simp only [d84431, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14241 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84432 q = 1) (hb : d99106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84432, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8118 q = 1) (hb : d84434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10108 q ha hb
    | true =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d8119 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d84436 q = 1) (hb : d99107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84436, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d84437 q = 1) (hb : d99108 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d99108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d84437, d99108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84438 q = 1) (hb : d99109 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d99109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d84438, d99109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84439 q = 1) (hb : d99110 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d99110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84439, d99110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14253 (p : Pattern) (ha : d84448 p = 1) (hb : d99117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84431 q = 1) (hb : d99105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14251 q ha hb
    | true =>
      simp only [d84431, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14241 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d99106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84432, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8118 q = 1) (hb : d84434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10108 q ha hb
    | true =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8119 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84436 q = 1) (hb : d99107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84446 q = 1) (hb : d99115 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d99115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d99115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84447 q = 1) (hb : d99116 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d99116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d99116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84448 q = 1) (hb : d99117 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d99117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d99117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14254 (p : Pattern) (ha : d8153 p = 1) (hb : d84469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8144 q = 1) (hb : d84460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10115 q ha hb
    | true =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8145 q = 1) (hb : d84461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8150 q = 1) (hb : d84466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d84466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8150, d84466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8151 q = 1) (hb : d84467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d84467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8151, d84467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8152 q = 1) (hb : d84468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d84468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8152, d84468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8153 q = 1) (hb : d84469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d84469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8153, d84469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14255 (p : Pattern) (ha : d84459 p = 1) (hb : d99124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2357 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
  have h2 (q : Pattern) (ha : d2358 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2359 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7161 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7161, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84458 q = 1) (hb : d99123 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84458, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84458, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84459 q = 1) (hb : d99124 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84459, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84459, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14256 (p : Pattern) (ha : d84465 p = 1) (hb : d99130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8140 q = 1) (hb : d84456 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d84456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10118 q ha hb
    | true =>
      simp only [d8140, d84456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8141 q = 1) (hb : d84457 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d84457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8141, d84457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84460 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14255 q ha hb
    | true =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84461 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84462 q = 1) (hb : d99127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84462, d99127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84462, d99127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84463 q = 1) (hb : d99128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84463, d99128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84463, d99128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84464 q = 1) (hb : d99129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84464, d99129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84464, d99129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84465 q = 1) (hb : d99130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84465, d99130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84465, d99130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14257 (p : Pattern) (ha : d84482 p = 1) (hb : d99136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84470 q = 1) (hb : d99131 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84470, d99131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14256 q ha hb
    | true =>
      simp only [d84470, d99131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14254 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d99132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d99132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84472, d99132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8169 q = 1) (hb : d84477 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d84477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10117 q ha hb
    | true =>
      simp only [d8169, d84477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8170 q = 1) (hb : d84478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d84478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8170, d84478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84479 q = 1) (hb : d99133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d99133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d99133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84480 q = 1) (hb : d99134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d99134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d99134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84481 q = 1) (hb : d99135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d99135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d99135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84482 q = 1) (hb : d99136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d99136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d99136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14258 (p : Pattern) (ha : d84488 p = 1) (hb : d99142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d84377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d84377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d84377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14240 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d84378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d84378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d84378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d84386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d84386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14240 q ha hb
    | true =>
      simp only [d8059, d84386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14242 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d84387 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d84387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d84387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d84388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d84388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d84388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84440 q = 1) (hb : d99111 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d99111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14248 q ha hb
    | true =>
      simp only [d84440, d99111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14252 q ha hb
  have h7 (q : Pattern) (ha : d8126 q = 1) (hb : d84442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d84442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14243 q ha hb
    | true =>
      simp only [d8126, d84442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d84443 q = 1) (hb : d99112 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d99112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84443, d99112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d84444 q = 1) (hb : d99113 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d99113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84444, d99113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84445 q = 1) (hb : d99114 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d99114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84445, d99114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84449 q = 1) (hb : d99118 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d99118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84449, d99118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14253 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d84450 q = 1) (hb : d99119 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d99119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84450, d99119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84451 q = 1) (hb : d99120 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d99120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84451, d99120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84452 q = 1) (hb : d99121 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d99121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84452, d99121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84453 q = 1) (hb : d99122 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d99122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84453, d99122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84483 q = 1) (hb : d99137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d99137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84483, d99137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14257 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d84484 q = 1) (hb : d99138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d99138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84484, d99138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84485 q = 1) (hb : d99139 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d99139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84485, d99139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84486 q = 1) (hb : d99140 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d99140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84486, d99140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84487 q = 1) (hb : d99141 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d99141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84487, d99141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84488 q = 1) (hb : d99142 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d99142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84488, d99142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14259 (p : Pattern) (ha : d84494 p = 1) (hb : d99148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d99143 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d99143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d99143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14258 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d99144 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d99144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d99144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d99145 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d99145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d99145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d99146 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d99146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d99146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d99147 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d99147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d99147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d99148 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d99148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d99148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14260 (p : Pattern) (ha : d84500 p = 1) (hb : d99154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d98903 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d98903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14154 q ha hb
    | true =>
      simp only [d83957, d98903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14175 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d98963 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d98963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d98963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14196 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d98964 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d98964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d98964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d99024 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d99024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d99024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14217 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d99025 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d99025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d99025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d99026 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d99026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d99026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d99086 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d99086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d99086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14238 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d99087 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d99087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d99087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d99088 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d99088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d99088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d99089 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d99089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d99089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d99149 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d99149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d99149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14259 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d99150 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d99150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d99150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d99151 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d99151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d99151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d99152 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d99152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d99152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d99153 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d99153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d99153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d99154 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d99154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d99154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro14261 (p : Pattern) (ha : d84506 p = 1) (hb : d99160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d99155 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d99155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14260 q ha hb
    | true =>
      simp only [d84501, d99155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d99156 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d99156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d99156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d99157 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d99157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d99157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d99158 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d99158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d99158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d99159 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d99159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d99159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d99160 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d99160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d99160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14262 (p : Pattern) (ha : d84512 p = 1) (hb : d99166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d99161 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d99161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14261 q ha hb
    | true =>
      simp only [d84507, d99161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d99162 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d99162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d99162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d99163 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d99163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d99163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d99164 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d99164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d99164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d99165 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d99165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d99165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d99166 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d99166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d99166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14263 (p : Pattern) (ha : d84518 p = 1) (hb : d99172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d99167 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d99167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14262 q ha hb
    | true =>
      simp only [d84513, d99167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d99168 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d99168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d99168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d99169 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d99169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d99169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d99170 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d99170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d99170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d99171 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d99171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d99171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d99172 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d99172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d99172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14264 (p : Pattern) (ha : d84524 p = 1) (hb : d99178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d99173 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d99173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14263 q ha hb
    | true =>
      simp only [d84519, d99173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d99174 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d99174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d99174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d99175 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d99175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d99175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d99176 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d99176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d99176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d99177 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d99177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d99177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d99178 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d99178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d99178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14265 (p : Pattern) (ha : d84530 p = 1) (hb : d99184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d99179 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d99179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14264 q ha hb
    | true =>
      simp only [d84525, d99179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d99180 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d99180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d99180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d99181 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d99181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d99181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d99182 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d99182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d99182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d99183 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d99183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d99183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d99184 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d99184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d99184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14266 (p : Pattern) (ha : d84536 p = 1) (hb : d99190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d99185 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d99185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14265 q ha hb
    | true =>
      simp only [d84531, d99185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d99186 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d99186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d99186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d99187 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d99187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d99187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d99188 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d99188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d99188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d99189 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d99189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d99189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d99190 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d99190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d99190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14267 (p : Pattern) (ha : d84542 p = 1) (hb : d99196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d99191 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d99191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14266 q ha hb
    | true =>
      simp only [d84537, d99191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d99192 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d99192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d99192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d99193 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d99193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d99193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d99194 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d99194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d99194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d99195 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d99195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d99195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d99196 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d99196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d99196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14268 (p : Pattern) (ha : d53655 p = 1) (hb : d98800 p = 1) : d99199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d98800 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d98800 q = 1) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13962 q ha hb
    | true =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d98800 q = 1) : d7305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d7305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d7305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d98800 q = 1) : d7306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d7306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d7306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d98800 q = 1) : d7307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d7307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d7307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d98800 q = 1) : d7308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d7308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d7308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d98800 q = 1) : d99199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14269 (p : Pattern) (ha : d53665 p = 1) (hb : d98800 p = 1) : d99209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d98800 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d98800 q = 1) : d7281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d7281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13964 q ha hb
    | true =>
      simp only [d244, d7281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d98800 q = 1) : d99205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d98800 q = 1) : d99206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d98800 q = 1) : d99207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d98800 q = 1) : d99208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d98800 q = 1) : d99209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14270 (p : Pattern) (ha : d53671 p = 1) (hb : d98800 p = 1) : d99215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d98800 q = 1) : d7310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d7310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13970 q ha hb
    | true =>
      simp only [d292, d7310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13971 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d98800 q = 1) : d7311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d7311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d7311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d98800 q = 1) : d99197 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d98800 q = 1) : d99198 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d98800 q = 1) : d99200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14268 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d98800 q = 1) : d99201 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d98800 q = 1) : d99202 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d98800 q = 1) : d99203 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d98800 q = 1) : d99204 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d98800 q = 1) : d99210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14269 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d98800 q = 1) : d99211 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d98800 q = 1) : d99212 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d98800 q = 1) : d99213 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d98800 q = 1) : d99214 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d98800 q = 1) : d99215 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14271 (p : Pattern) (ha : d53677 p = 1) (hb : d98800 p = 1) : d99221 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d98800 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d98800 q = 1) : d99216 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14270 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d98800 q = 1) : d99217 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d98800 q = 1) : d99218 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d98800 q = 1) : d99219 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d98800 q = 1) : d99220 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d98800 q = 1) : d99221 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14272 (p : Pattern) (ha : d53680 p = 1) (hb : d98800 p = 1) : d99224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d98800 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d502 q = 1) (hb : d98800 q = 1) : d7443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d7443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13993 q ha hb
    | true =>
      simp only [d502, d7443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d98800 q = 1) : d7444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d7444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d7444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d98800 q = 1) : d7445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d7445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d7445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d98800 q = 1) : d7446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d7446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d7446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d98800 q = 1) : d7447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d7447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d7447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d98800 q = 1) : d99224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14273 (p : Pattern) (ha : d689 p = 1) (hb : d98800 p = 1) : d7539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d686 q = 1) (hb : d98800 q = 1) : d7536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d98800, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d98800, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d687 q = 1) (hb : d98800 q = 1) : d7537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d687, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d688 q = 1) (hb : d98800 q = 1) : d7538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d688, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d689 q = 1) (hb : d98800 q = 1) : d7539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d689, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14274 (p : Pattern) (ha : d53691 p = 1) (hb : d98800 p = 1) : d99235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d98800 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53686 q = 1) (hb : d98800 q = 1) : d99230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14273 q ha hb
    | true =>
      simp only [d53686, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53687 q = 1) (hb : d98800 q = 1) : d99231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53688 q = 1) (hb : d98800 q = 1) : d99232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53688, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53689 q = 1) (hb : d98800 q = 1) : d99233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53690 q = 1) (hb : d98800 q = 1) : d99234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53691 q = 1) (hb : d98800 q = 1) : d99235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14275 (p : Pattern) (ha : d53697 p = 1) (hb : d98800 p = 1) : d99241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d98800 q = 1) : d7449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13992 q ha hb
    | true =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13994 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d98800 q = 1) : d7450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d98800 q = 1) : d99222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d98800 q = 1) : d99223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d98800 q = 1) : d99225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14272 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d98800 q = 1) : d99226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d98800 q = 1) : d99227 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d98800 q = 1) : d99228 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d98800 q = 1) : d99229 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d98800 q = 1) : d99236 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14274 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d98800 q = 1) : d99237 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d98800 q = 1) : d99238 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d98800 q = 1) : d99239 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d98800 q = 1) : d99240 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d98800 q = 1) : d99241 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14276 (p : Pattern) (ha : d53703 p = 1) (hb : d98800 p = 1) : d99247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d98800 q = 1) : d99242 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14275 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d98800 q = 1) : d99243 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d98800 q = 1) : d99244 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d98800 q = 1) : d99245 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d98800 q = 1) : d99246 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d98800 q = 1) : d99247 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14277 (p : Pattern) (ha : d53707 p = 1) (hb : d98800 p = 1) : d99251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d98800 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d794 q = 1) (hb : d98800 q = 1) : d7591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14019 q ha hb
    | true =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d98800 q = 1) : d7592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d98800 q = 1) : d7593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d98800 q = 1) : d7594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d98800 q = 1) : d7595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d98800 q = 1) : d99251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14278 (p : Pattern) (ha : d1011 p = 1) (hb : d98800 p = 1) : d7691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8227 q ha hb
    | true =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d92315 q = 1) : d1007 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1008 q = 1) (hb : d98800 q = 1) : d7688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d98800, d7688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d98800, d7688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d98800 q = 1) : d7689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d7689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1009, d7689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d98800 q = 1) : d7690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d7690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d7690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d98800 q = 1) : d7691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d7691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d7691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14279 (p : Pattern) (ha : d53718 p = 1) (hb : d98800 p = 1) : d99262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d98800 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53713 q = 1) (hb : d98800 q = 1) : d99257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14278 q ha hb
    | true =>
      simp only [d53713, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53714 q = 1) (hb : d98800 q = 1) : d99258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53715 q = 1) (hb : d98800 q = 1) : d99259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53715, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53716 q = 1) (hb : d98800 q = 1) : d99260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53717 q = 1) (hb : d98800 q = 1) : d99261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53718 q = 1) (hb : d98800 q = 1) : d99262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14280 (p : Pattern) (ha : d53724 p = 1) (hb : d98800 p = 1) : d99268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d98800 q = 1) : d7597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d7597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14018 q ha hb
    | true =>
      simp only [d800, d7597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14020 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d98800 q = 1) : d7598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d7598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d7598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d98800 q = 1) : d99249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d98800 q = 1) : d99250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d98800 q = 1) : d99252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14277 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d98800 q = 1) : d99253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d98800 q = 1) : d99254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d98800 q = 1) : d99255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d98800 q = 1) : d99256 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d98800 q = 1) : d99263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14279 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d98800 q = 1) : d99264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d98800 q = 1) : d99265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d98800 q = 1) : d99266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d98800 q = 1) : d99267 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d98800 q = 1) : d99268 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14281 (p : Pattern) (ha : d53730 p = 1) (hb : d98800 p = 1) : d99274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d98800 q = 1) : d99269 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14280 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d98800 q = 1) : d99270 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d98800 q = 1) : d99271 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d98800 q = 1) : d99272 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d98800 q = 1) : d99273 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d98800 q = 1) : d99274 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14282 (p : Pattern) (ha : d53735 p = 1) (hb : d98800 p = 1) : d99279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d98800 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1173 q = 1) (hb : d98800 q = 1) : d7744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d7744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14045 q ha hb
    | true =>
      simp only [d1173, d7744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d98800 q = 1) : d7745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d7745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d7745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d98800 q = 1) : d7746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d7746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d7746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d98800 q = 1) : d7747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d7747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d7747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d98800 q = 1) : d7748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d7748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d7748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d98800 q = 1) : d99279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14283 (p : Pattern) (ha : d1436 p = 1) (hb : d98800 p = 1) : d7844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8255 q ha hb
    | true =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d92315 q = 1) : d1432 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1433 q = 1) (hb : d98800 q = 1) : d7841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d98800, d7841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d98800, d7841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d98800 q = 1) : d7842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d7842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1434, d7842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d98800 q = 1) : d7843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d7843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d7843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d98800 q = 1) : d7844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d7844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d7844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14284 (p : Pattern) (ha : d53746 p = 1) (hb : d98800 p = 1) : d99290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d98800 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53741 q = 1) (hb : d98800 q = 1) : d99285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14283 q ha hb
    | true =>
      simp only [d53741, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53742 q = 1) (hb : d98800 q = 1) : d99286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53743 q = 1) (hb : d98800 q = 1) : d99287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53743, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53744 q = 1) (hb : d98800 q = 1) : d99288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53745 q = 1) (hb : d98800 q = 1) : d99289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53746 q = 1) (hb : d98800 q = 1) : d99290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14285 (p : Pattern) (ha : d53752 p = 1) (hb : d98800 p = 1) : d99296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d98800 q = 1) : d7750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d7750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14044 q ha hb
    | true =>
      simp only [d1179, d7750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14046 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d98800 q = 1) : d7751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d7751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d7751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d98800 q = 1) : d99277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d98800 q = 1) : d99278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d98800 q = 1) : d99280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14282 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d98800 q = 1) : d99281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d98800 q = 1) : d99282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d98800 q = 1) : d99283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d98800 q = 1) : d99284 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d98800 q = 1) : d99291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14284 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d98800 q = 1) : d99292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d98800 q = 1) : d99293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d98800 q = 1) : d99294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d98800 q = 1) : d99295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d98800 q = 1) : d99296 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14286 (p : Pattern) (ha : d53758 p = 1) (hb : d98800 p = 1) : d99302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d98800 q = 1) : d99297 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14285 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d98800 q = 1) : d99298 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d98800 q = 1) : d99299 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d98800 q = 1) : d99300 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d98800 q = 1) : d99301 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d98800 q = 1) : d99302 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14287 (p : Pattern) (ha : d53764 p = 1) (hb : d98800 p = 1) : d99308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d98800 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1634 q = 1) (hb : d98800 q = 1) : d7898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d7898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14071 q ha hb
    | true =>
      simp only [d1634, d7898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d98800 q = 1) : d7899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d7899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d7899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d98800 q = 1) : d7900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d7900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d7900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d98800 q = 1) : d7901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d7901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d7901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d98800 q = 1) : d7902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d7902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d7902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d98800 q = 1) : d99308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14288 (p : Pattern) (ha : d1913 p = 1) (hb : d98800 p = 1) : d7998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8283 q ha hb
    | true =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d92315 q = 1) : d1909 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1910 q = 1) (hb : d98800 q = 1) : d7995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d98800, d7995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d98800, d7995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d98800 q = 1) : d7996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d7996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1911, d7996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d98800 q = 1) : d7997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d7997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d7997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d98800 q = 1) : d7998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d7998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d7998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14289 (p : Pattern) (ha : d53775 p = 1) (hb : d98800 p = 1) : d99319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d98800 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53770 q = 1) (hb : d98800 q = 1) : d99314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14288 q ha hb
    | true =>
      simp only [d53770, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53771 q = 1) (hb : d98800 q = 1) : d99315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53772 q = 1) (hb : d98800 q = 1) : d99316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53772, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53773 q = 1) (hb : d98800 q = 1) : d99317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53774 q = 1) (hb : d98800 q = 1) : d99318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53775 q = 1) (hb : d98800 q = 1) : d99319 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14290 (p : Pattern) (ha : d53781 p = 1) (hb : d98800 p = 1) : d99325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d98800 q = 1) : d7904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d7904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14070 q ha hb
    | true =>
      simp only [d1640, d7904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14072 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d98800 q = 1) : d7905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d7905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d7905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d98800 q = 1) : d99306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d98800 q = 1) : d99307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d98800 q = 1) : d99309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14287 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d98800 q = 1) : d99310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d98800 q = 1) : d99311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d98800 q = 1) : d99312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d98800 q = 1) : d99313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d98800 q = 1) : d99320 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14289 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d98800 q = 1) : d99321 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d98800 q = 1) : d99322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d98800 q = 1) : d99323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d98800 q = 1) : d99324 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d98800 q = 1) : d99325 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14291 (p : Pattern) (ha : d53787 p = 1) (hb : d98800 p = 1) : d99331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d98800 q = 1) : d99326 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14290 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d98800 q = 1) : d99327 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d98800 q = 1) : d99328 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d98800 q = 1) : d99329 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d98800 q = 1) : d99330 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d98800 q = 1) : d99331 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14292 (p : Pattern) (ha : d53794 p = 1) (hb : d98800 p = 1) : d99338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d98800 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2117 q = 1) (hb : d98800 q = 1) : d8053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d8053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14097 q ha hb
    | true =>
      simp only [d2117, d8053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d98800 q = 1) : d8054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d8054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d8054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2119 q = 1) (hb : d98800 q = 1) : d8055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d8055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, d8055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2120 q = 1) (hb : d98800 q = 1) : d8056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d8056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d8056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2121 q = 1) (hb : d98800 q = 1) : d8057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d8057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d8057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53794 q = 1) (hb : d98800 q = 1) : d99338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14293 (p : Pattern) (ha : d2391 p = 1) (hb : d98800 p = 1) : d8153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8311 q ha hb
    | true =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d92315 q = 1) : d2387 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2388 q = 1) (hb : d98800 q = 1) : d8150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d98800, d8150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, d98800, d8150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2389 q = 1) (hb : d98800 q = 1) : d8151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d8151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2389, d8151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2390 q = 1) (hb : d98800 q = 1) : d8152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d8152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2390, d8152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2391 q = 1) (hb : d98800 q = 1) : d8153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d8153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2391, d8153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14294 (p : Pattern) (ha : d53805 p = 1) (hb : d98800 p = 1) : d99349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d98800 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53800 q = 1) (hb : d98800 q = 1) : d99344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14293 q ha hb
    | true =>
      simp only [d53800, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53801 q = 1) (hb : d98800 q = 1) : d99345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53802 q = 1) (hb : d98800 q = 1) : d99346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53802, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53803 q = 1) (hb : d98800 q = 1) : d99347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53804 q = 1) (hb : d98800 q = 1) : d99348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53805 q = 1) (hb : d98800 q = 1) : d99349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14295 (p : Pattern) (ha : d53811 p = 1) (hb : d98800 p = 1) : d99355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d98800 q = 1) : d8059 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d8059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14096 q ha hb
    | true =>
      simp only [d2123, d8059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14098 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d98800 q = 1) : d8060 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d8060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d8060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d98800 q = 1) : d99336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d98800 q = 1) : d99337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d98800 q = 1) : d99339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14292 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d98800 q = 1) : d99340 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d98800 q = 1) : d99341 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d98800 q = 1) : d99342 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d98800 q = 1) : d99343 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d98800 q = 1) : d99350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14294 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d98800 q = 1) : d99351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d98800 q = 1) : d99352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d98800 q = 1) : d99353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d98800 q = 1) : d99354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d98800 q = 1) : d99355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14296 (p : Pattern) (ha : d53817 p = 1) (hb : d98800 p = 1) : d99361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d98800 q = 1) : d99356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14295 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d98800 q = 1) : d99357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d98800 q = 1) : d99358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d98800 q = 1) : d99359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d98800 q = 1) : d99360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d98800 q = 1) : d99361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14297 (p : Pattern) (ha : d53823 p = 1) (hb : d98800 p = 1) : d99367 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d98800 q = 1) : d99248 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14271 q ha hb
    | true =>
      simp only [d53704, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14276 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d98800 q = 1) : d99275 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14281 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d98800 q = 1) : d99276 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d98800 q = 1) : d99303 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14286 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d98800 q = 1) : d99304 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d98800 q = 1) : d99305 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d98800 q = 1) : d99332 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14291 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d98800 q = 1) : d99333 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d98800 q = 1) : d99334 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d98800 q = 1) : d99335 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d98800 q = 1) : d99362 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14296 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d98800 q = 1) : d99363 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d98800 q = 1) : d99364 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d98800 q = 1) : d99365 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d98800 q = 1) : d99366 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d98800 q = 1) : d99367 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro14298 (p : Pattern) (ha : d53829 p = 1) (hb : d98800 p = 1) : d99373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d98800 q = 1) : d99368 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14297 q ha hb
    | true =>
      simp only [d53824, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d98800 q = 1) : d99369 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d98800 q = 1) : d99370 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d98800 q = 1) : d99371 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d98800 q = 1) : d99372 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d98800 q = 1) : d99373 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14299 (p : Pattern) (ha : d53835 p = 1) (hb : d98800 p = 1) : d99379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d98800 q = 1) : d99374 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14298 q ha hb
    | true =>
      simp only [d53830, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d98800 q = 1) : d99375 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d98800 q = 1) : d99376 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d98800 q = 1) : d99377 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d98800 q = 1) : d99378 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d98800 q = 1) : d99379 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14300 (p : Pattern) (ha : d53841 p = 1) (hb : d98800 p = 1) : d99385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d98800 q = 1) : d99380 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14299 q ha hb
    | true =>
      simp only [d53836, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d98800 q = 1) : d99381 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d98800 q = 1) : d99382 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d98800 q = 1) : d99383 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d98800 q = 1) : d99384 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d98800 q = 1) : d99385 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14301 (p : Pattern) (ha : d53847 p = 1) (hb : d98800 p = 1) : d99391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d98800 q = 1) : d99386 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14300 q ha hb
    | true =>
      simp only [d53842, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d98800 q = 1) : d99387 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d98800 q = 1) : d99388 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d98800 q = 1) : d99389 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d98800 q = 1) : d99390 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d98800 q = 1) : d99391 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14302 (p : Pattern) (ha : d53853 p = 1) (hb : d98801 p = 1) : d99397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d98800 q = 1) : d99392 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14301 q ha hb
    | true =>
      simp only [d53848, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d98800 q = 1) : d99393 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53850 q = 1) (hb : d98801 q = 1) : d99394 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d98801, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d98801, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53851 q = 1) (hb : d98801 q = 1) : d99395 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53851, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53852 q = 1) (hb : d98801 q = 1) : d99396 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53852, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53853 q = 1) (hb : d98801 q = 1) : d99397 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53853, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14303 (p : Pattern) (ha : d53859 p = 1) (hb : d98801 p = 1) : d99403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d98801 q = 1) : d99398 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14302 q ha hb
    | true =>
      simp only [d53854, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d98801 q = 1) : d99399 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d98801 q = 1) : d99400 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d98801 q = 1) : d99401 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d98801 q = 1) : d99402 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d98801 q = 1) : d99403 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14304 (p : Pattern) (ha : d53865 p = 1) (hb : d98801 p = 1) : d99409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d98801 q = 1) : d99404 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14303 q ha hb
    | true =>
      simp only [d53860, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d98801 q = 1) : d99405 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d98801 q = 1) : d99406 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d98801 q = 1) : d99407 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d98801 q = 1) : d99408 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d98801 q = 1) : d99409 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14305 (p : Pattern) (ha : d7302 p = 1) (hb : d83767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d7298 q = 1) (hb : d83757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7298, d83757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7299 q = 1) (hb : d83764 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7299, d83764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7300 q = 1) (hb : d83765 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7300, d83765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7301 q = 1) (hb : d83766 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7301, d83766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7302 q = 1) (hb : d83767 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d83767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d83767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14306 (p : Pattern) (ha : d7309 p = 1) (hb : d83786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d7298 q = 1) (hb : d83757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7298, d83757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7299 q = 1) (hb : d83764 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7299, d83764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7300 q = 1) (hb : d83765 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7300, d83765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7301 q = 1) (hb : d83766 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d83766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83772 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83776 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7255 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q ha hb
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d7305 q = 1) (hb : d83779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d83779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7305, d83779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7306 q = 1) (hb : d83783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d83783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7306, d83783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7307 q = 1) (hb : d83784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d83784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7307, d83784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7308 q = 1) (hb : d83785 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d83785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7308, d83785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7309 q = 1) (hb : d83786 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d83786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7309, d83786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14307 (p : Pattern) (ha : d83795 p = 1) (hb : d99199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q ha hb
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d83779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d83779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7305, d83779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7306 q = 1) (hb : d83783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d83783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d83783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7307 q = 1) (hb : d83793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d83793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d83793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7308 q = 1) (hb : d83794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d83794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d83794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83795 q = 1) (hb : d99199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14308 (p : Pattern) (ha : d83820 p = 1) (hb : d99209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14134 q ha hb
    | true =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d99205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83810, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83817 q = 1) (hb : d99206 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83818 q = 1) (hb : d99207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83819 q = 1) (hb : d99208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83820 q = 1) (hb : d99209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14309 (p : Pattern) (ha : d83826 p = 1) (hb : d99215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d83787 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d83787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14305 q ha hb
    | true =>
      simp only [d7310, d83787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14306 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7311 q = 1) (hb : d83790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d83790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d83790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83791 q = 1) (hb : d99197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83791, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83792 q = 1) (hb : d99198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83792, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83796 q = 1) (hb : d99200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83796, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14307 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83797 q = 1) (hb : d99201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83797, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83798 q = 1) (hb : d99202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83798, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83799 q = 1) (hb : d99203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83799, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83800 q = 1) (hb : d99204 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83800, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83821 q = 1) (hb : d99210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83821, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14308 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83822 q = 1) (hb : d99211 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83822, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83823 q = 1) (hb : d99212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83823, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83824 q = 1) (hb : d99213 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83824, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83825 q = 1) (hb : d99214 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83825, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83826 q = 1) (hb : d99215 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83826, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14310 (p : Pattern) (ha : d83832 p = 1) (hb : d99221 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d83827 q = 1) (hb : d99216 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83827, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14309 q ha hb
  have h8 (q : Pattern) (ha : d83828 q = 1) (hb : d99217 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83828, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83829 q = 1) (hb : d99218 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83829, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83830 q = 1) (hb : d99219 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83830, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83831 q = 1) (hb : d99220 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83831, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83832 q = 1) (hb : d99221 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d83832, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro14311 (p : Pattern) (ha : d7439 p = 1) (hb : d83886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7434 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q ha hb
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h5 (q : Pattern) (ha : d7435 q = 1) (hb : d83876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7435, d83876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7436 q = 1) (hb : d83883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7436, d83883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7437 q = 1) (hb : d83884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7437, d83884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7438 q = 1) (hb : d83885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7438, d83885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7439 q = 1) (hb : d83886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d83886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d83886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14312 (p : Pattern) (ha : d7448 p = 1) (hb : d83905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7434 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q ha hb
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d7435 q = 1) (hb : d83876 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7435, d83876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7436 q = 1) (hb : d83883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7436, d83883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7437 q = 1) (hb : d83884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7437, d83884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7438 q = 1) (hb : d83885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d83885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83895 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7443 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14157 q ha hb
    | true =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h13 (q : Pattern) (ha : d7444 q = 1) (hb : d83898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d83898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7444, d83898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7445 q = 1) (hb : d83902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d83902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7445, d83902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7446 q = 1) (hb : d83903 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d83903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7446, d83903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7447 q = 1) (hb : d83904 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d83904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7447, d83904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7448 q = 1) (hb : d83905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d83905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7448, d83905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14313 (p : Pattern) (ha : d83914 p = 1) (hb : d99224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7443 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14157 q ha hb
    | true =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d83898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d83898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7444, d83898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7445 q = 1) (hb : d83902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d83902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d83902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7446 q = 1) (hb : d83912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d83912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d83912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7447 q = 1) (hb : d83913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d83913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d83913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83914 q = 1) (hb : d99224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14314 (p : Pattern) (ha : d83944 p = 1) (hb : d99235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83933 q = 1) (hb : d99230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83933, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14170 q hb ha
    | true =>
      simp only [d83933, d99230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d99231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83934, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83941 q = 1) (hb : d99232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83942 q = 1) (hb : d99233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83943 q = 1) (hb : d99234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83944 q = 1) (hb : d99235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14315 (p : Pattern) (ha : d83950 p = 1) (hb : d99241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d83906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d83906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14311 q ha hb
    | true =>
      simp only [d7449, d83906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14312 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7450 q = 1) (hb : d83909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d83909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d83909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83910 q = 1) (hb : d99222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83910, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83911 q = 1) (hb : d99223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83911, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83915 q = 1) (hb : d99225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83915, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14313 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83916 q = 1) (hb : d99226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83916, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83917 q = 1) (hb : d99227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83917, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83918 q = 1) (hb : d99228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83918, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83919 q = 1) (hb : d99229 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83919, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83945 q = 1) (hb : d99236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83945, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14314 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83946 q = 1) (hb : d99237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83946, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83947 q = 1) (hb : d99238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83947, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83948 q = 1) (hb : d99239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83948, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83949 q = 1) (hb : d99240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83949, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83950 q = 1) (hb : d99241 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83950, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14316 (p : Pattern) (ha : d83956 p = 1) (hb : d99247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d99242 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14315 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d99243 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d99244 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d99245 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d99246 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d99247 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14317 (p : Pattern) (ha : d7587 p = 1) (hb : d84015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7582 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q ha hb
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h5 (q : Pattern) (ha : d7583 q = 1) (hb : d84005 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d84005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7583, d84005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7584 q = 1) (hb : d84012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d84012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7584, d84012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7585 q = 1) (hb : d84013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d84013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7585, d84013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7586 q = 1) (hb : d84014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d84014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7586, d84014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7587 q = 1) (hb : d84015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d84015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d84015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14318 (p : Pattern) (ha : d7596 p = 1) (hb : d84034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7582 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q ha hb
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d7583 q = 1) (hb : d84005 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d84005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7583, d84005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7584 q = 1) (hb : d84012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d84012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7584, d84012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7585 q = 1) (hb : d84013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d84013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7585, d84013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7586 q = 1) (hb : d84014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d84014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d84014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84020 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7591 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14178 q ha hb
    | true =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h13 (q : Pattern) (ha : d7592 q = 1) (hb : d84027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d84027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7592, d84027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7593 q = 1) (hb : d84031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d84031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7593, d84031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7594 q = 1) (hb : d84032 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d84032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7594, d84032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7595 q = 1) (hb : d84033 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d84033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7595, d84033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7596 q = 1) (hb : d84034 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d84034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7596, d84034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14319 (p : Pattern) (ha : d84043 p = 1) (hb : d99251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7591 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14178 q ha hb
    | true =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d84027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d84027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7592, d84027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7593 q = 1) (hb : d84031 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d84031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d84031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7594 q = 1) (hb : d84041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d84041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d84041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7595 q = 1) (hb : d84042 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d84042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d84042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84043 q = 1) (hb : d99251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14320 (p : Pattern) (ha : d84077 p = 1) (hb : d99262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84066 q = 1) (hb : d99257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84066, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14191 q hb ha
    | true =>
      simp only [d84066, d99257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d99258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84067, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84074 q = 1) (hb : d99259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84075 q = 1) (hb : d99260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84076 q = 1) (hb : d99261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84077 q = 1) (hb : d99262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14321 (p : Pattern) (ha : d84083 p = 1) (hb : d99268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d84035 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d84035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14317 q ha hb
    | true =>
      simp only [d7597, d84035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14318 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7598 q = 1) (hb : d84038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d84038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d84038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84039 q = 1) (hb : d99249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84039, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84040 q = 1) (hb : d99250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84040, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84044 q = 1) (hb : d99252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84044, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14319 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84045 q = 1) (hb : d99253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84045, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84046 q = 1) (hb : d99254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84046, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84047 q = 1) (hb : d99255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84047, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84048 q = 1) (hb : d99256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84048, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84078 q = 1) (hb : d99263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84078, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14320 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84079 q = 1) (hb : d99264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84079, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84080 q = 1) (hb : d99265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84080, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84081 q = 1) (hb : d99266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84081, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84082 q = 1) (hb : d99267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84082, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84083 q = 1) (hb : d99268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84083, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14322 (p : Pattern) (ha : d84089 p = 1) (hb : d99274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d99269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14321 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d99270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d99271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d99272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d99273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d99274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14323 (p : Pattern) (ha : d7740 p = 1) (hb : d84149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7735 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q ha hb
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h5 (q : Pattern) (ha : d7736 q = 1) (hb : d84139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7736, d84139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7737 q = 1) (hb : d84146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7737, d84146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7738 q = 1) (hb : d84147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7738, d84147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7739 q = 1) (hb : d84148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7739, d84148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7740 q = 1) (hb : d84149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d84149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d84149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14324 (p : Pattern) (ha : d7749 p = 1) (hb : d84168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7735 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q ha hb
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d7736 q = 1) (hb : d84139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7736, d84139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7737 q = 1) (hb : d84146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7737, d84146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7738 q = 1) (hb : d84147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7738, d84147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7739 q = 1) (hb : d84148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84154 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7744 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14199 q ha hb
    | true =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h13 (q : Pattern) (ha : d7745 q = 1) (hb : d84161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7745, d84161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7746 q = 1) (hb : d84165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7746, d84165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7747 q = 1) (hb : d84166 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7747, d84166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7748 q = 1) (hb : d84167 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7748, d84167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7749 q = 1) (hb : d84168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d84168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7749, d84168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14325 (p : Pattern) (ha : d84177 p = 1) (hb : d99279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7744 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14199 q ha hb
    | true =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d84161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7745, d84161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7746 q = 1) (hb : d84165 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d84165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7747 q = 1) (hb : d84175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d84175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7748 q = 1) (hb : d84176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d84176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84177 q = 1) (hb : d99279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14326 (p : Pattern) (ha : d84211 p = 1) (hb : d99290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84200 q = 1) (hb : d99285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84200, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14212 q hb ha
    | true =>
      simp only [d84200, d99285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d99286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84201, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84208 q = 1) (hb : d99287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84209 q = 1) (hb : d99288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84210 q = 1) (hb : d99289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84211 q = 1) (hb : d99290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14327 (p : Pattern) (ha : d84217 p = 1) (hb : d99296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d84169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d84169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14323 q ha hb
    | true =>
      simp only [d7750, d84169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14324 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7751 q = 1) (hb : d84172 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d84172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d84172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84173 q = 1) (hb : d99277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84173, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84174 q = 1) (hb : d99278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84174, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84178 q = 1) (hb : d99280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84178, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14325 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84179 q = 1) (hb : d99281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84179, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84180 q = 1) (hb : d99282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84180, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84181 q = 1) (hb : d99283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84181, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84182 q = 1) (hb : d99284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84182, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84212 q = 1) (hb : d99291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84212, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14326 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84213 q = 1) (hb : d99292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84213, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84214 q = 1) (hb : d99293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84214, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84215 q = 1) (hb : d99294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84215, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84216 q = 1) (hb : d99295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84216, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84217 q = 1) (hb : d99296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84217, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14328 (p : Pattern) (ha : d84223 p = 1) (hb : d99302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d99297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14327 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d99298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d99299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d99300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d99301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d99302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14329 (p : Pattern) (ha : d7894 p = 1) (hb : d84284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7889 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q ha hb
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h5 (q : Pattern) (ha : d7890 q = 1) (hb : d84274 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7890, d84274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7891 q = 1) (hb : d84281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7891, d84281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7892 q = 1) (hb : d84282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7892, d84282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7893 q = 1) (hb : d84283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7893, d84283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7894 q = 1) (hb : d84284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d84284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d84284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14330 (p : Pattern) (ha : d7903 p = 1) (hb : d84303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7889 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q ha hb
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d7890 q = 1) (hb : d84274 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7890, d84274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7891 q = 1) (hb : d84281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7891, d84281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7892 q = 1) (hb : d84282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7892, d84282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7893 q = 1) (hb : d84283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84293 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d7898 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14220 q ha hb
    | true =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h13 (q : Pattern) (ha : d7899 q = 1) (hb : d84296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7899, d84296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7900 q = 1) (hb : d84300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7900, d84300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7901 q = 1) (hb : d84301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7901, d84301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7902 q = 1) (hb : d84302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7902, d84302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7903 q = 1) (hb : d84303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d84303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7903, d84303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14331 (p : Pattern) (ha : d84312 p = 1) (hb : d99308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7898 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14220 q ha hb
    | true =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d84296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7899, d84296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7900 q = 1) (hb : d84300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d84300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7901 q = 1) (hb : d84310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d84310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7902 q = 1) (hb : d84311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d84311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84312 q = 1) (hb : d99308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14332 (p : Pattern) (ha : d84346 p = 1) (hb : d99319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84335 q = 1) (hb : d99314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84335, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14233 q hb ha
    | true =>
      simp only [d84335, d99314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d99315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84336, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84343 q = 1) (hb : d99316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84344 q = 1) (hb : d99317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84345 q = 1) (hb : d99318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84346 q = 1) (hb : d99319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14333 (p : Pattern) (ha : d84352 p = 1) (hb : d99325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d84304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d84304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14329 q ha hb
    | true =>
      simp only [d7904, d84304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14330 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7905 q = 1) (hb : d84307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d84307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d84307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84308 q = 1) (hb : d99306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84308, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84309 q = 1) (hb : d99307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84309, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84313 q = 1) (hb : d99309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84313, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14331 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84314 q = 1) (hb : d99310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84314, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84315 q = 1) (hb : d99311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84315, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84316 q = 1) (hb : d99312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84316, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84317 q = 1) (hb : d99313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84317, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84347 q = 1) (hb : d99320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84347, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14332 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84348 q = 1) (hb : d99321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84348, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84349 q = 1) (hb : d99322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84349, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84350 q = 1) (hb : d99323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84350, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84351 q = 1) (hb : d99324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84351, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84352 q = 1) (hb : d99325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84352, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14334 (p : Pattern) (ha : d84358 p = 1) (hb : d99331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d99326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14333 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d99327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d99328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d99329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d99330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d99331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14335 (p : Pattern) (ha : d8049 p = 1) (hb : d84420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8044 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q ha hb
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h5 (q : Pattern) (ha : d8045 q = 1) (hb : d84410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8045, d84410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8046 q = 1) (hb : d84417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8046, d84417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8047 q = 1) (hb : d84418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8047, d84418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8048 q = 1) (hb : d84419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8048, d84419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8049 q = 1) (hb : d84420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d84420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d84420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14336 (p : Pattern) (ha : d8058 p = 1) (hb : d84439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8044 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q ha hb
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d8045 q = 1) (hb : d84410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8045, d84410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8046 q = 1) (hb : d84417 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8046, d84417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8047 q = 1) (hb : d84418 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8047, d84418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8048 q = 1) (hb : d84419 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d84419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84425 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d8053 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14241 q ha hb
    | true =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h13 (q : Pattern) (ha : d8054 q = 1) (hb : d84432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d84432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8054, d84432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8055 q = 1) (hb : d84436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d84436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8055, d84436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8056 q = 1) (hb : d84437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d84437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8056, d84437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8057 q = 1) (hb : d84438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d84438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8057, d84438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8058 q = 1) (hb : d84439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d84439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8058, d84439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14337 (p : Pattern) (ha : d84448 p = 1) (hb : d99338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8053 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14241 q ha hb
    | true =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d84432 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d84432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8054, d84432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8055 q = 1) (hb : d84436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d84436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d84436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8056 q = 1) (hb : d84446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d84446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d84446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8057 q = 1) (hb : d84447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d84447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d84447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84448 q = 1) (hb : d99338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14338 (p : Pattern) (ha : d84482 p = 1) (hb : d99349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84471 q = 1) (hb : d99344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84471, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14254 q hb ha
    | true =>
      simp only [d84471, d99344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d99345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84472, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84479 q = 1) (hb : d99346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84480 q = 1) (hb : d99347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84481 q = 1) (hb : d99348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84482 q = 1) (hb : d99349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14339 (p : Pattern) (ha : d84488 p = 1) (hb : d99355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d84440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d84440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14335 q ha hb
    | true =>
      simp only [d8059, d84440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14336 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8060 q = 1) (hb : d84443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d84443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d84443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84444 q = 1) (hb : d99336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84444, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84445 q = 1) (hb : d99337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84445, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84449 q = 1) (hb : d99339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84449, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14337 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84450 q = 1) (hb : d99340 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84450, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84451 q = 1) (hb : d99341 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84451, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84452 q = 1) (hb : d99342 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84452, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84453 q = 1) (hb : d99343 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84453, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84483 q = 1) (hb : d99350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84483, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14338 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84484 q = 1) (hb : d99351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84484, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84485 q = 1) (hb : d99352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84485, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84486 q = 1) (hb : d99353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84486, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84487 q = 1) (hb : d99354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84487, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84488 q = 1) (hb : d99355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84488, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14340 (p : Pattern) (ha : d84494 p = 1) (hb : d99361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d99356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14339 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d99357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d99358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d99359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d99360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d99361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14341 (p : Pattern) (ha : d84500 p = 1) (hb : d99367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d99248 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14310 q ha hb
    | true =>
      simp only [d83957, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14316 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d99275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14322 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d99276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d99303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14328 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d99304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d99305 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d99332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14334 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d99333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d99334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d99335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d99362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14340 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d99363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d99364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d99365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d99366 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d99367 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro14342 (p : Pattern) (ha : d84506 p = 1) (hb : d99373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d99368 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14341 q ha hb
    | true =>
      simp only [d84501, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d99369 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d99370 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d99371 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d99372 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d99373 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14343 (p : Pattern) (ha : d84512 p = 1) (hb : d99379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d99374 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14342 q ha hb
    | true =>
      simp only [d84507, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d99375 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d99376 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d99377 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d99378 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d99379 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14344 (p : Pattern) (ha : d84518 p = 1) (hb : d99385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d99380 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14343 q ha hb
    | true =>
      simp only [d84513, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d99381 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d99382 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d99383 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d99384 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d99385 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14345 (p : Pattern) (ha : d84524 p = 1) (hb : d99391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d99386 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14344 q ha hb
    | true =>
      simp only [d84519, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d99387 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d99388 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d99389 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d99390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d99391 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14346 (p : Pattern) (ha : d84530 p = 1) (hb : d99397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d99392 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14345 q ha hb
    | true =>
      simp only [d84525, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d99393 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d99394 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d99395 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d99396 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d99397 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14347 (p : Pattern) (ha : d84536 p = 1) (hb : d99403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d99398 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14346 q ha hb
    | true =>
      simp only [d84531, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d99399 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d99400 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d99401 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d99402 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d99403 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14348 (p : Pattern) (ha : d84542 p = 1) (hb : d99409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d99404 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14347 q ha hb
    | true =>
      simp only [d84537, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d99405 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d99406 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d99407 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d99408 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d99409 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro14349 (p : Pattern) (ha : d7302 p = 1) (hb : d85432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7298 q = 1) (hb : d85428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7298, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7299 q = 1) (hb : d85429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7299, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7300 q = 1) (hb : d85430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7300, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7301 q = 1) (hb : d85431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7301, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7302 q = 1) (hb : d85432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14350 (p : Pattern) (ha : d7309 p = 1) (hb : d85437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7248 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7298 q = 1) (hb : d85428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7298, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7299 q = 1) (hb : d85429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7299, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7300 q = 1) (hb : d85430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7300, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7301 q = 1) (hb : d85431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7358 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7362 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7255 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7305 q = 1) (hb : d85433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7305, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7306 q = 1) (hb : d85434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7306, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7307 q = 1) (hb : d85435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7307, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7308 q = 1) (hb : d85436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7308, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7309 q = 1) (hb : d85437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7309, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14351 (p : Pattern) (ha : d85444 p = 1) (hb : d99199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d85433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7305, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7306 q = 1) (hb : d85434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7307 q = 1) (hb : d85442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7308 q = 1) (hb : d85443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d99199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d99199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14352 (p : Pattern) (ha : d85454 p = 1) (hb : d99209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85450 q = 1) (hb : d99205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85450, d99205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d99206 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85451, d99206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d99207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d99207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d99208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d99208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d99209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d99209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14353 (p : Pattern) (ha : d85460 p = 1) (hb : d99215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d85438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14349 q ha hb
    | true =>
      simp only [d7310, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14350 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7311 q = 1) (hb : d85439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85440 q = 1) (hb : d99197 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85440, d99197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85441 q = 1) (hb : d99198 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85441, d99198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85445 q = 1) (hb : d99200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85445, d99200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14351 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85446 q = 1) (hb : d99201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85446, d99201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85447 q = 1) (hb : d99202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85447, d99202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85448 q = 1) (hb : d99203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85448, d99203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85449 q = 1) (hb : d99204 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85449, d99204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85455 q = 1) (hb : d99210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85455, d99210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14352 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85456 q = 1) (hb : d99211 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85456, d99211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85457 q = 1) (hb : d99212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85457, d99212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85458 q = 1) (hb : d99213 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85458, d99213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85459 q = 1) (hb : d99214 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85459, d99214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85460 q = 1) (hb : d99215 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85460, d99215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14354 (p : Pattern) (ha : d85466 p = 1) (hb : d99221 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d99216 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d99216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14353 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d99217 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d99217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d99218 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d99218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d99219 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d99219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d99220 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d99220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d99221 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d85466, d99221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro14355 (p : Pattern) (ha : d7439 p = 1) (hb : d85471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7434 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7435 q = 1) (hb : d85467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7435, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7436 q = 1) (hb : d85468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7436, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7437 q = 1) (hb : d85469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7437, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7438 q = 1) (hb : d85470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7438, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7439 q = 1) (hb : d85471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14356 (p : Pattern) (ha : d7448 p = 1) (hb : d85476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7434 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7435 q = 1) (hb : d85467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7435, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7436 q = 1) (hb : d85468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7436, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7437 q = 1) (hb : d85469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7437, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7438 q = 1) (hb : d85470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7443 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7444 q = 1) (hb : d85472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7444, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7445 q = 1) (hb : d85473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7445, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7446 q = 1) (hb : d85474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7446, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7447 q = 1) (hb : d85475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7447, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7448 q = 1) (hb : d85476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7448, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14357 (p : Pattern) (ha : d85483 p = 1) (hb : d99224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7443 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d85472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7444, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7445 q = 1) (hb : d85473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7446 q = 1) (hb : d85481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7447 q = 1) (hb : d85482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d99224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d99224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14358 (p : Pattern) (ha : d85493 p = 1) (hb : d99235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99230 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85489 q = 1) (hb : d99231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85489, d99231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d99232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85490, d99232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d99233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d99233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d99234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d99234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d99235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d99235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14359 (p : Pattern) (ha : d85499 p = 1) (hb : d99241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d85477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14355 q ha hb
    | true =>
      simp only [d7449, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14356 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7516 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7450 q = 1) (hb : d85478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85479 q = 1) (hb : d99222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85479, d99222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85480 q = 1) (hb : d99223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85480, d99223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85484 q = 1) (hb : d99225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85484, d99225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14357 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85485 q = 1) (hb : d99226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85485, d99226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85486 q = 1) (hb : d99227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85486, d99227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85487 q = 1) (hb : d99228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85487, d99228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85488 q = 1) (hb : d99229 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85488, d99229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85494 q = 1) (hb : d99236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85494, d99236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14358 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85495 q = 1) (hb : d99237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85495, d99237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85496 q = 1) (hb : d99238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85496, d99238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85497 q = 1) (hb : d99239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85497, d99239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85498 q = 1) (hb : d99240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85498, d99240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85499 q = 1) (hb : d99241 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85499, d99241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14360 (p : Pattern) (ha : d85505 p = 1) (hb : d99247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d99242 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d99242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14359 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d99243 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d99243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d99244 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d99244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d99245 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d99245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d99246 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d99246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d99247 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d99247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14361 (p : Pattern) (ha : d7587 p = 1) (hb : d85511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7582 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7583 q = 1) (hb : d85507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7583, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7584 q = 1) (hb : d85508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7584, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7585 q = 1) (hb : d85509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7585, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7586 q = 1) (hb : d85510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7586, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7587 q = 1) (hb : d85511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d85511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d85511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14362 (p : Pattern) (ha : d7596 p = 1) (hb : d85516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7582 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7583 q = 1) (hb : d85507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7583, d85507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7584 q = 1) (hb : d85508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7584, d85508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7585 q = 1) (hb : d85509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7585, d85509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7586 q = 1) (hb : d85510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d85510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7649 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7591 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7592 q = 1) (hb : d85512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7592, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7593 q = 1) (hb : d85513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7593, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7594 q = 1) (hb : d85514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d85514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7594, d85514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7595 q = 1) (hb : d85515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d85515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7595, d85515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7596 q = 1) (hb : d85516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d85516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7596, d85516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14363 (p : Pattern) (ha : d85523 p = 1) (hb : d99251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d85512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7592, d85512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7593 q = 1) (hb : d85513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d85513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7594 q = 1) (hb : d85521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d85521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d85521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7595 q = 1) (hb : d85522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d85522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d85522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d99251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d99251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14364 (p : Pattern) (ha : d85533 p = 1) (hb : d99262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85529 q = 1) (hb : d99258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85529, d99258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d99259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85530, d99259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d99260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d99260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d99261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d99261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d99262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d99262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14365 (p : Pattern) (ha : d85539 p = 1) (hb : d99268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d85517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d85517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14361 q ha hb
    | true =>
      simp only [d7597, d85517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14362 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7598 q = 1) (hb : d85518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d85518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d85518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85519 q = 1) (hb : d99249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85519, d99249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85520 q = 1) (hb : d99250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85520, d99250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85524 q = 1) (hb : d99252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85524, d99252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14363 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85525 q = 1) (hb : d99253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85525, d99253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85526 q = 1) (hb : d99254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85526, d99254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85527 q = 1) (hb : d99255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85527, d99255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85528 q = 1) (hb : d99256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85528, d99256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85534 q = 1) (hb : d99263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85534, d99263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14364 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85535 q = 1) (hb : d99264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85535, d99264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85536 q = 1) (hb : d99265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85536, d99265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85537 q = 1) (hb : d99266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85537, d99266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85538 q = 1) (hb : d99267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85538, d99267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85539 q = 1) (hb : d99268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85539, d99268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14366 (p : Pattern) (ha : d85545 p = 1) (hb : d99274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d99269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d99269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14365 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d99270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d99270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d99271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d99271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d99272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d99272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d99273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d99273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d99274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d99274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14367 (p : Pattern) (ha : d7740 p = 1) (hb : d85552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7735 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7736 q = 1) (hb : d85548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7736, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7737 q = 1) (hb : d85549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7737, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7738 q = 1) (hb : d85550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7738, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7739 q = 1) (hb : d85551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7739, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7740 q = 1) (hb : d85552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d85552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d85552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14368 (p : Pattern) (ha : d7749 p = 1) (hb : d85557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7735 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7736 q = 1) (hb : d85548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7736, d85548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7737 q = 1) (hb : d85549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7737, d85549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7738 q = 1) (hb : d85550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7738, d85550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7739 q = 1) (hb : d85551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d85551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7798 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7802 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7744 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7745 q = 1) (hb : d85553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7745, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7746 q = 1) (hb : d85554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7746, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7747 q = 1) (hb : d85555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d85555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7747, d85555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7748 q = 1) (hb : d85556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d85556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7748, d85556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7749 q = 1) (hb : d85557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d85557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7749, d85557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14369 (p : Pattern) (ha : d85564 p = 1) (hb : d99279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7744 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d85553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7745, d85553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7746 q = 1) (hb : d85554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d85554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7747 q = 1) (hb : d85562 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d85562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d85562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7748 q = 1) (hb : d85563 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d85563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d85563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d99279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d99279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14370 (p : Pattern) (ha : d85574 p = 1) (hb : d99290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85570 q = 1) (hb : d99286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85570, d99286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d99287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85571, d99287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d99288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d99288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d99289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d99289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d99290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d99290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14371 (p : Pattern) (ha : d85580 p = 1) (hb : d99296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d85558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d85558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14367 q ha hb
    | true =>
      simp only [d7750, d85558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14368 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7751 q = 1) (hb : d85559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d85559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d85559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85560 q = 1) (hb : d99277 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85560, d99277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85561 q = 1) (hb : d99278 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85561, d99278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85565 q = 1) (hb : d99280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85565, d99280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14369 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85566 q = 1) (hb : d99281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85566, d99281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85567 q = 1) (hb : d99282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85567, d99282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85568 q = 1) (hb : d99283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85568, d99283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85569 q = 1) (hb : d99284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85569, d99284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85575 q = 1) (hb : d99291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85575, d99291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14370 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85576 q = 1) (hb : d99292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85576, d99292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85577 q = 1) (hb : d99293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85577, d99293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85578 q = 1) (hb : d99294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85578, d99294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85579 q = 1) (hb : d99295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85579, d99295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85580 q = 1) (hb : d99296 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85580, d99296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14372 (p : Pattern) (ha : d85586 p = 1) (hb : d99302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d99297 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d99297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14371 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d99298 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d99298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d99299 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d99299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d99300 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d99300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d99301 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d99301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d99302 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d99302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14373 (p : Pattern) (ha : d7894 p = 1) (hb : d85594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7889 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7890 q = 1) (hb : d85590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7890, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7891 q = 1) (hb : d85591 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7891, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7892 q = 1) (hb : d85592 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7892, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7893 q = 1) (hb : d85593 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7893, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7894 q = 1) (hb : d85594 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d85594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d85594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14374 (p : Pattern) (ha : d7903 p = 1) (hb : d85599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7889 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7890 q = 1) (hb : d85590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7890, d85590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7891 q = 1) (hb : d85591 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7891, d85591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7892 q = 1) (hb : d85592 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7892, d85592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7893 q = 1) (hb : d85593 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d85593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d7898 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7899 q = 1) (hb : d85595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7899, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d7900 q = 1) (hb : d85596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d7900, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7901 q = 1) (hb : d85597 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d85597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d7901, d85597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d7902 q = 1) (hb : d85598 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d85598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7902, d85598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7903 q = 1) (hb : d85599 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d85599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7903, d85599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14375 (p : Pattern) (ha : d85606 p = 1) (hb : d99308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7898 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d85595 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7899, d85595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7900 q = 1) (hb : d85596 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d85596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7901 q = 1) (hb : d85604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d85604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d85604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7902 q = 1) (hb : d85605 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d85605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d85605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d99308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d99308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14376 (p : Pattern) (ha : d85616 p = 1) (hb : d99319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85612 q = 1) (hb : d99315 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85612, d99315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d99316 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85613, d99316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d99317 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d99317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d99318 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d99318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d99319 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d99319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14377 (p : Pattern) (ha : d85622 p = 1) (hb : d99325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d85600 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d85600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14373 q ha hb
    | true =>
      simp only [d7904, d85600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14374 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7971 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7905 q = 1) (hb : d85601 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d85601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d85601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85602 q = 1) (hb : d99306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85602, d99306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85603 q = 1) (hb : d99307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85603, d99307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85607 q = 1) (hb : d99309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85607, d99309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14375 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85608 q = 1) (hb : d99310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85608, d99310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85609 q = 1) (hb : d99311 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85609, d99311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85610 q = 1) (hb : d99312 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85610, d99312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85611 q = 1) (hb : d99313 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85611, d99313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85617 q = 1) (hb : d99320 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85617, d99320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14376 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85618 q = 1) (hb : d99321 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85618, d99321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85619 q = 1) (hb : d99322 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85619, d99322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85620 q = 1) (hb : d99323 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85620, d99323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85621 q = 1) (hb : d99324 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85621, d99324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85622 q = 1) (hb : d99325 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85622, d99325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14378 (p : Pattern) (ha : d85628 p = 1) (hb : d99331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d99326 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d99326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14377 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d99327 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d99327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d99328 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d99328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d99329 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d99329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d99330 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d99330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d99331 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d99331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14379 (p : Pattern) (ha : d8049 p = 1) (hb : d85637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8044 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8045 q = 1) (hb : d85633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8045, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8046 q = 1) (hb : d85634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8046, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8047 q = 1) (hb : d85635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8047, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8048 q = 1) (hb : d85636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8048, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8049 q = 1) (hb : d85637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d85637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d85637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14380 (p : Pattern) (ha : d8058 p = 1) (hb : d85642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8045 q = 1) (hb : d85633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8045, d85633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d8046 q = 1) (hb : d85634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8046, d85634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8047 q = 1) (hb : d85635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8047, d85635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8048 q = 1) (hb : d85636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d85636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8107 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8111 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d8053 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d8054 q = 1) (hb : d85638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8054, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d8055 q = 1) (hb : d85639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d8055, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d8056 q = 1) (hb : d85640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d85640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8056, d85640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8057 q = 1) (hb : d85641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d85641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8057, d85641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8058 q = 1) (hb : d85642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d85642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8058, d85642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro14381 (p : Pattern) (ha : d85649 p = 1) (hb : d99338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8053 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d85638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8054, d85638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8055 q = 1) (hb : d85639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d85639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8056 q = 1) (hb : d85647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d85647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d85647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8057 q = 1) (hb : d85648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d85648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d85648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d99338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d99338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro14382 (p : Pattern) (ha : d85659 p = 1) (hb : d99349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d99344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85655 q = 1) (hb : d99345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85655, d99345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d99346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85656, d99346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d99347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d99347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d99348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d99348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d99349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d99349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14383 (p : Pattern) (ha : d85665 p = 1) (hb : d99355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8061 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d85643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14379 q ha hb
    | true =>
      simp only [d8059, d85643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14380 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8060 q = 1) (hb : d85644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d85644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85645 q = 1) (hb : d99336 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85645, d99336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85646 q = 1) (hb : d99337 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85646, d99337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85650 q = 1) (hb : d99339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85650, d99339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14381 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85651 q = 1) (hb : d99340 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85651, d99340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85652 q = 1) (hb : d99341 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85652, d99341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85653 q = 1) (hb : d99342 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85653, d99342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85654 q = 1) (hb : d99343 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85654, d99343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85660 q = 1) (hb : d99350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85660, d99350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14382 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85661 q = 1) (hb : d99351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85661, d99351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85662 q = 1) (hb : d99352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85662, d99352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85663 q = 1) (hb : d99353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85663, d99353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85664 q = 1) (hb : d99354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85664, d99354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85665 q = 1) (hb : d99355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85665, d99355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14384 (p : Pattern) (ha : d85671 p = 1) (hb : d99361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d99356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d99356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14383 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d99357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d99357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d99358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d99358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d99359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d99359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d99360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d99360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d99361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d99361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14385 (p : Pattern) (ha : d85677 p = 1) (hb : d99367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d99248 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14354 q ha hb
    | true =>
      simp only [d85506, d99248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14360 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d99275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d99275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14366 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d99276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d99276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d99303 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d99303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14372 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d99304 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d99304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d99305 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d99305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d99332 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d99332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14378 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d99333 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d99333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d99334 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d99334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d99335 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d99335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d99362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d99362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14384 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d99363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d99363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d99364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d99364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d99365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d99365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d99366 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d99366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d99367 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d99367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro14386 (p : Pattern) (ha : d85683 p = 1) (hb : d99373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d99368 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14385 q ha hb
    | true =>
      simp only [d85678, d99368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d99369 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d99369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d99370 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d99370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d99371 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d99371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d99372 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d99372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d99373 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d99373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14387 (p : Pattern) (ha : d85689 p = 1) (hb : d99379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d99374 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14386 q ha hb
    | true =>
      simp only [d85684, d99374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d99375 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d99375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d99376 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d99376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d99377 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d99377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d99378 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d99378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d99379 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d99379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14388 (p : Pattern) (ha : d85695 p = 1) (hb : d99385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d99380 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14387 q ha hb
    | true =>
      simp only [d85690, d99380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d99381 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d99381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d99382 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d99382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d99383 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d99383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d99384 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d99384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d99385 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d99385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14389 (p : Pattern) (ha : d85701 p = 1) (hb : d99391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d99386 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14388 q ha hb
    | true =>
      simp only [d85696, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d99387 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d99388 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d99389 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d99390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d99391 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14390 (p : Pattern) (ha : d85707 p = 1) (hb : d99397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d99392 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14389 q ha hb
    | true =>
      simp only [d85702, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d99393 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d99394 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d99395 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d99396 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d99397 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14391 (p : Pattern) (ha : d85713 p = 1) (hb : d99403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d99398 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14390 q ha hb
    | true =>
      simp only [d85708, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d99399 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d99400 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d99401 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d99402 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d99403 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14392 (p : Pattern) (ha : d85719 p = 1) (hb : d99409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d99404 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14391 q ha hb
    | true =>
      simp only [d85714, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d99405 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d99406 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d99407 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d99408 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d99409 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14393 (p : Pattern) (ha : d0 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14394 (p : Pattern) (ha : d0 p = 1) (hb : d82331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82331 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14395 (p : Pattern) (ha : d0 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14396 (p : Pattern) (ha : d0 p = 1) (hb : d89603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89603 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14397 (p : Pattern) (ha : d0 p = 1) (hb : d100607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100607 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14398 (p : Pattern) (ha : d0 p = 1) (hb : d100898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100898 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14399 (p : Pattern) (ha : d0 p = 1) (hb : d100900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100900 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14400 (p : Pattern) (ha : d0 p = 1) (hb : d100902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100902 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14401 (p : Pattern) (ha : d0 p = 1) (hb : d93269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d93269 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14402 (p : Pattern) (ha : d0 p = 1) (hb : d94516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94516 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14403 (p : Pattern) (ha : d0 p = 1) (hb : d100899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100899 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14404 (p : Pattern) (ha : d0 p = 1) (hb : d100907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100907 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14405 (p : Pattern) (ha : d0 p = 1) (hb : d98791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98791 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14406 (p : Pattern) (ha : d0 p = 1) (hb : d100937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100937 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14407 (p : Pattern) (ha : d0 p = 1) (hb : d100940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100940 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14408 (p : Pattern) (ha : d0 p = 1) (hb : d100942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14409 (p : Pattern) (ha : d0 p = 1) (hb : d101874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101874 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14410 (p : Pattern) (ha : d0 p = 1) (hb : d102050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102050 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14411 (p : Pattern) (ha : d0 p = 1) (hb : d100941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14412 (p : Pattern) (ha : d0 p = 1) (hb : d102055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14413 (p : Pattern) (ha : d0 p = 1) (hb : d82407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82407 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14414 (p : Pattern) (ha : d0 p = 1) (hb : d102105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14415 (p : Pattern) (ha : d74837 p = 1) (hb : d74854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74853 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74835 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d74854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74835, d74854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74836 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74837 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro14416 (p : Pattern) (ha : d74843 p = 1) (hb : d74854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14415 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14417 (p : Pattern) (ha : d74849 p = 1) (hb : d74854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14416 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d74854 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14418 (p : Pattern) (ha : d0 p = 1) (hb : d102592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102592 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14419 (p : Pattern) (ha : d0 p = 1) (hb : d102349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102349 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14420 (p : Pattern) (ha : d74849 p = 1) (hb : d102593 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d102593 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14421 (p : Pattern) (ha : d53865 p = 1) (hb : d102593 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d102593 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14422 (p : Pattern) (ha : d74831 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74828 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74829 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d102597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74829, d102597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74830 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74831 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d102598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74831, d102598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14423 (p : Pattern) (ha : d74837 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14422 q ha hb
    | true =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14424 (p : Pattern) (ha : d74843 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14423 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14425 (p : Pattern) (ha : d74849 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14424 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14426 (p : Pattern) (ha : d53847 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53845 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d102597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53845, d102597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53846 q = 1) (hb : d102597 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d102598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53847, d102598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14427 (p : Pattern) (ha : d53853 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14426 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14428 (p : Pattern) (ha : d53859 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14427 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14429 (p : Pattern) (ha : d53865 p = 1) (hb : d102598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14428 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d102598 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14430 (p : Pattern) (ha : d74849 p = 1) (hb : d82693 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d82693 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14431 (p : Pattern) (ha : d53865 p = 1) (hb : d82693 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d82693 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14432 (p : Pattern) (ha : d74831 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74829 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74830 q = 1) (hb : d102600 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d102600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74830, d102600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74831 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d102601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74831, d102601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14433 (p : Pattern) (ha : d74837 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14432 q ha hb
    | true =>
      simp only [d74832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14434 (p : Pattern) (ha : d74843 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14433 q ha hb
    | true =>
      simp only [d74838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14435 (p : Pattern) (ha : d74849 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14434 q ha hb
    | true =>
      simp only [d74844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14436 (p : Pattern) (ha : d0 p = 1) (hb : d104241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104241 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14437 (p : Pattern) (ha : d53847 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53846 q = 1) (hb : d102600 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d102600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53846, d102600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53847 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d102601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53847, d102601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14438 (p : Pattern) (ha : d53853 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14437 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14439 (p : Pattern) (ha : d53859 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14438 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14440 (p : Pattern) (ha : d53865 p = 1) (hb : d102601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14439 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d102601 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14441 (p : Pattern) (ha : d0 p = 1) (hb : d104532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104532 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14442 (p : Pattern) (ha : d74849 p = 1) (hb : d104540 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d104540 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14443 (p : Pattern) (ha : d53865 p = 1) (hb : d104540 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d104540 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14444 (p : Pattern) (ha : d74849 p = 1) (hb : d104541 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d104541 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14445 (p : Pattern) (ha : d53865 p = 1) (hb : d104541 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d104541 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro14446 (p : Pattern) (ha : d203 p = 1) (hb : d77842 p = 1) : d7254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d77842 q = 1) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d77842 q = 1) : d7246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d7246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d7246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d77842 q = 1) : d7254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d7254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d7254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14447 (p : Pattern) (ha : d4349 p = 1) (hb : d77842 p = 1) : d85406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d77842 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d77842 q = 1) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14446 q ha hb
    | true =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d77842 q = 1) : d85395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d77842 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d77842 q = 1) : d85396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d77842 q = 1) : d85404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d77842 q = 1) : d85405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d77842 q = 1) : d85406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14448 (p : Pattern) (ha : d243 p = 1) (hb : d77842 p = 1) : d7280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d77842 q = 1) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8172 q ha hb
    | true =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d77842 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d77842 q = 1) : d7277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d7277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d7277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d77842 q = 1) : d7278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d7278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d7278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d77842 q = 1) : d7279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d7279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d7279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d77842 q = 1) : d7280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d7280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d7280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14449 (p : Pattern) (ha : d4359 p = 1) (hb : d77842 p = 1) : d85416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d77842 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d77842 q = 1) : d7281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d7281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14448 q ha hb
    | true =>
      simp only [d244, d7281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d77842 q = 1) : d85412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d77842 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d77842 q = 1) : d85413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d77842 q = 1) : d85414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d77842 q = 1) : d85415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d77842 q = 1) : d85416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14450 (p : Pattern) (ha : d156 p = 1) (hb : d77842 p = 1) : d7247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d77842 q = 1) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d77842 q = 1) : d7246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d7246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d7246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d77842 q = 1) : d7247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d7247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d7247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14451 (p : Pattern) (ha : d51643 p = 1) (hb : d77842 p = 1) : d85394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d77842 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d77842 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d77842 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d77842 q = 1) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
    | true =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d77842 q = 1) : d85390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d77842 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d77842 q = 1) : d85391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d77842 q = 1) : d85392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d77842 q = 1) : d85393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d77842 q = 1) : d85394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14452 (p : Pattern) (ha : d51646 p = 1) (hb : d77842 p = 1) : d85399 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d77842 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d77842 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d77842 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d77842 q = 1) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
    | true =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d77842 q = 1) : d85390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d77842 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d77842 q = 1) : d85391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d77842 q = 1) : d85392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d77842 q = 1) : d85393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d77842 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d77842 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d77842 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d77842 q = 1) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14446 q ha hb
    | true =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d77842 q = 1) : d85395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d77842 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d77842 q = 1) : d85396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d77842 q = 1) : d85397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d77842 q = 1) : d85398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d77842 q = 1) : d85399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro14453 (p : Pattern) (ha : d51652 p = 1) (hb : d77842 p = 1) : d85422 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d77842 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d77842 q = 1) : d85400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14451 q ha hb
    | true =>
      simp only [d51647, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14452 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d77842 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d77842 q = 1) : d85401 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d77842 q = 1) : d85402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d77842 q = 1) : d85403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d77842 q = 1) : d85407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14447 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d77842 q = 1) : d85408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d77842 q = 1) : d85409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d77842 q = 1) : d85410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d77842 q = 1) : d85411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d77842 q = 1) : d85417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14449 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d77842 q = 1) : d85418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d77842 q = 1) : d85419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d77842 q = 1) : d85420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d77842 q = 1) : d85421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d77842 q = 1) : d85422 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14454 (p : Pattern) (ha : d284 p = 1) (hb : d77842 p = 1) : d7302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d77842 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d77842 q = 1) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
    | true =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d77842 q = 1) : d7298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d77842 q = 1) : d7299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d77842 q = 1) : d7300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d77842 q = 1) : d7301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d77842 q = 1) : d7302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d7302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d7302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14455 (p : Pattern) (ha : d291 p = 1) (hb : d77842 p = 1) : d7309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d77842 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d77842 q = 1) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
    | true =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d77842 q = 1) : d7298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d77842 q = 1) : d7299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d77842 q = 1) : d7300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d77842 q = 1) : d7301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d77842 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d77842 q = 1) : d7255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14446 q ha hb
    | true =>
      simp only [d204, d7255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d77842 q = 1) : d7305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d7305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d7305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d77842 q = 1) : d7306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d7306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d7306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d77842 q = 1) : d7307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d7307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d7307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d77842 q = 1) : d7308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d7308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d7308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d77842 q = 1) : d7309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d7309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d7309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14456 (p : Pattern) (ha : d397 p = 1) (hb : d77842 p = 1) : d7376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d77842 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d77842 q = 1) : d7248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
    | true =>
      simp only [d157, d7248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d77842 q = 1) : d7298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d7298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d77842 q = 1) : d7299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d7299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d77842 q = 1) : d7300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d7300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d77842 q = 1) : d7301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d7301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d77842 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d77842 q = 1) : d7376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d7376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d7376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14457 (p : Pattern) (ha : d296 p = 1) (hb : d77842 p = 1) : d7314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d77842 q = 1) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d77842 q = 1) : d7313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d7313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d7313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d77842 q = 1) : d7314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d7314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d7314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14458 (p : Pattern) (ha : d303 p = 1) (hb : d77842 p = 1) : d7321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d77842 q = 1) : d7319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d7319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d7319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d77842 q = 1) : d7320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d7320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d7320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d77842 q = 1) : d7321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d7321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d7321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14459 (p : Pattern) (ha : d336 p = 1) (hb : d77842 p = 1) : d7332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9813 q ha hb
    | true =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d77842 q = 1) : d7329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d7329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d7329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d77842 q = 1) : d7330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d7330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d7330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d77842 q = 1) : d7331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d7331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d7331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d336 q = 1) (hb : d77842 q = 1) : d7332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d7332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d7332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14460 (p : Pattern) (ha : d4736 p = 1) (hb : d77842 p = 1) : d7347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d77842 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d77842 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d77842 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d77842 q = 1) : d7347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14461 (p : Pattern) (ha : d74579 p = 1) (hb : d77842 p = 1) : d85432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d77842 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d77842 q = 1) : d7315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d7315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14457 q ha hb
    | true =>
      simp only [d297, d7315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d77842 q = 1) : d7316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d7316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d7316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d77842 q = 1) : d7317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d7317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d7317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d77842 q = 1) : d7318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d7318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d7318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d77842 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d77842 q = 1) : d7322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d7322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14458 q ha hb
    | true =>
      simp only [d304, d7322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d77842 q = 1) : d7323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d7323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d7323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d77842 q = 1) : d7324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d7324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d7324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d77842 q = 1) : d7333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d7333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14459 q ha hb
    | true =>
      simp only [d337, d7333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d77842 q = 1) : d85428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d77842 q = 1) : d7348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14460 q ha hb
    | true =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d77842 q = 1) : d7349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d77842 q = 1) : d85429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d77842 q = 1) : d85430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d77842 q = 1) : d85431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74579 q = 1) (hb : d77842 q = 1) : d85432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74579, d85432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14462 (p : Pattern) (ha : d376 p = 1) (hb : d77842 p = 1) : d7354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d77842 q = 1) : d7245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d7245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d77842 q = 1) : d7313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d7313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d7313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d77842 q = 1) : d7354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d7354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d7354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14463 (p : Pattern) (ha : d381 p = 1) (hb : d77842 p = 1) : d7359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d77842 q = 1) : d7244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d7244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d77842 q = 1) : d7319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d7319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d7319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d77842 q = 1) : d7320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d7320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d7320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d77842 q = 1) : d7359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d7359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d7359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14464 (p : Pattern) (ha : d385 p = 1) (hb : d77842 p = 1) : d7363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9813 q ha hb
    | true =>
      simp only [d331, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d332 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d332, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d333 q = 1) (hb : d77842 q = 1) : d7329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d7329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d333, d7329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d334 q = 1) (hb : d77842 q = 1) : d7330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d7330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d334, d7330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d335 q = 1) (hb : d77842 q = 1) : d7331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d7331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d335, d7331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d385 q = 1) (hb : d77842 q = 1) : d7363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d385, d7363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d385, d7363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14465 (p : Pattern) (ha : d5355 p = 1) (hb : d77842 p = 1) : d7368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d77842 q = 1) : d7242 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8164 q ha hb
    | true =>
      simp only [d151, d7242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d7243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d77842 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d77842 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d77842 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d77842 q = 1) : d7368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14466 (p : Pattern) (ha : d74583 p = 1) (hb : d77842 p = 1) : d85437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d77842 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d77842 q = 1) : d7315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d7315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14457 q ha hb
    | true =>
      simp only [d297, d7315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d77842 q = 1) : d7316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d7316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d7316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d77842 q = 1) : d7317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d7317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d7317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d77842 q = 1) : d7318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d7318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d7318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d77842 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d77842 q = 1) : d7322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d7322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14458 q ha hb
    | true =>
      simp only [d304, d7322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d77842 q = 1) : d7323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d7323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d7323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d77842 q = 1) : d7324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d7324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d7324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d337 q = 1) (hb : d77842 q = 1) : d7333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d7333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14459 q ha hb
    | true =>
      simp only [d337, d7333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14450 q ha hb
  have h11 (q : Pattern) (ha : d4371 q = 1) (hb : d77842 q = 1) : d85428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4371, d85428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d77842 q = 1) : d7348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14460 q ha hb
    | true =>
      simp only [d4737, d7348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d77842 q = 1) : d7349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74576 q = 1) (hb : d77842 q = 1) : d85429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74576, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74576, d85429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74577 q = 1) (hb : d77842 q = 1) : d85430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74577, d85430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74578 q = 1) (hb : d77842 q = 1) : d85431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74578, d85431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d77842 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d77842 q = 1) : d7355 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d7355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14462 q ha hb
    | true =>
      simp only [d377, d7355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d77842 q = 1) : d7356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d7356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d7356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d77842 q = 1) : d7357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d7357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d7357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d77842 q = 1) : d7358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d7358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d7358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d77842 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d77842 q = 1) : d7360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d7360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14463 q ha hb
    | true =>
      simp only [d382, d7360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d77842 q = 1) : d7361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d7361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d7361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d77842 q = 1) : d7362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d7362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d7362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d386 q = 1) (hb : d77842 q = 1) : d7364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d7364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14464 q ha hb
    | true =>
      simp only [d386, d7364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14446 q ha hb
  have h27 (q : Pattern) (ha : d4376 q = 1) (hb : d77842 q = 1) : d85433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4376, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d77842 q = 1) : d7369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14465 q ha hb
    | true =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d77842 q = 1) : d7370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d74580 q = 1) (hb : d77842 q = 1) : d85434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d74580, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74581 q = 1) (hb : d77842 q = 1) : d85435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74581, d85435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d74582 q = 1) (hb : d77842 q = 1) : d85436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74582, d85436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d74583 q = 1) (hb : d77842 q = 1) : d85437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74583, d85437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14467 (p : Pattern) (ha : d74590 p = 1) (hb : d77842 p = 1) : d85444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d77842 q = 1) : d7364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d7364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14464 q ha hb
    | true =>
      simp only [d386, d7364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14446 q ha hb
  have h2 (q : Pattern) (ha : d4376 q = 1) (hb : d77842 q = 1) : d85433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d85433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d77842 q = 1) : d7369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14465 q ha hb
    | true =>
      simp only [d5356, d7369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d77842 q = 1) : d7370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74580 q = 1) (hb : d77842 q = 1) : d85434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74580, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74580, d85434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74588 q = 1) (hb : d77842 q = 1) : d85442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74588, d85442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74589 q = 1) (hb : d77842 q = 1) : d85443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74589, d85443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d77842 q = 1) : d85444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d85444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d85444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14468 (p : Pattern) (ha : d429 p = 1) (hb : d77842 p = 1) : d7396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d424 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9821 q ha hb
    | true =>
      simp only [d424, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d425 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d425, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d425, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d77842 q = 1) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8172 q ha hb
    | true =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d426 q = 1) (hb : d77842 q = 1) : d7393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d426, d7393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d426, d7393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d427 q = 1) (hb : d77842 q = 1) : d7394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d427, d7394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d427, d7394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d428 q = 1) (hb : d77842 q = 1) : d7395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d428, d7395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d428, d7395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d429 q = 1) (hb : d77842 q = 1) : d7396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d429, d7396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d429, d7396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14469 (p : Pattern) (ha : d5377 p = 1) (hb : d77842 p = 1) : d7411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d77842 q = 1) : d7275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8172 q ha hb
    | true =>
      simp only [d238, d7275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d7276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d77842 q = 1) : d7408 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d77842 q = 1) : d7409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d77842 q = 1) : d7410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d77842 q = 1) : d7411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14470 (p : Pattern) (ha : d74599 p = 1) (hb : d77842 p = 1) : d85454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d77842 q = 1) : d7397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d7397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14468 q ha hb
    | true =>
      simp only [d430, d7397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14448 q ha hb
  have h2 (q : Pattern) (ha : d4391 q = 1) (hb : d77842 q = 1) : d85450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d85450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d85450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d77842 q = 1) : d7412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d7412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14469 q ha hb
    | true =>
      simp only [d5378, d7412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d77842 q = 1) : d7413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d77842 q = 1) : d85451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d85451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74596, d85451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d77842 q = 1) : d85452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d85452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d85452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d77842 q = 1) : d85453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d85453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d85453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d77842 q = 1) : d85454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d85454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d85454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14471 (p : Pattern) (ha : d74605 p = 1) (hb : d77842 p = 1) : d85460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d77842 q = 1) : d7303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d7303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d7303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14454 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d77842 q = 1) : d7304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d7304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d7304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d77842 q = 1) : d7310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d7310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14454 q ha hb
    | true =>
      simp only [d292, d7310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14455 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d77842 q = 1) : d7311 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d7311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d7311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d77842 q = 1) : d7312 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d7312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d7312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74584 q = 1) (hb : d77842 q = 1) : d85438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14461 q ha hb
    | true =>
      simp only [d74584, d85438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14466 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d77842 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d77842 q = 1) : d7377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d7377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14456 q ha hb
    | true =>
      simp only [d398, d7377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74585 q = 1) (hb : d77842 q = 1) : d85439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74585, d85439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74586 q = 1) (hb : d77842 q = 1) : d85440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d85440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74586, d85440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d74587 q = 1) (hb : d77842 q = 1) : d85441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d85441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74587, d85441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74591 q = 1) (hb : d77842 q = 1) : d85445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d85445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74591, d85445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14467 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d77842 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d74592 q = 1) (hb : d77842 q = 1) : d85446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d85446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74592, d85446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74593 q = 1) (hb : d77842 q = 1) : d85447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d85447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74593, d85447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74594 q = 1) (hb : d77842 q = 1) : d85448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d85448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74594, d85448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d74595 q = 1) (hb : d77842 q = 1) : d85449 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d85449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74595, d85449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74600 q = 1) (hb : d77842 q = 1) : d85455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d85455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74600, d85455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14470 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d77842 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d74601 q = 1) (hb : d77842 q = 1) : d85456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d85456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74601, d85456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d74602 q = 1) (hb : d77842 q = 1) : d85457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d85457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74602, d85457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74603 q = 1) (hb : d77842 q = 1) : d85458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d85458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74603, d85458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74604 q = 1) (hb : d77842 q = 1) : d85459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d85459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74604, d85459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d74605 q = 1) (hb : d77842 q = 1) : d85460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d85460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74605, d85460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14472 (p : Pattern) (ha : d74611 p = 1) (hb : d77842 p = 1) : d85466 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d77842 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d77842 q = 1) : d85423 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14453 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d77842 q = 1) : d85424 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d77842 q = 1) : d85425 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d77842 q = 1) : d85426 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d77842 q = 1) : d85427 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74606 q = 1) (hb : d77842 q = 1) : d85461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d85461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74606, d85461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14471 q ha hb
  have h8 (q : Pattern) (ha : d74607 q = 1) (hb : d77842 q = 1) : d85462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d85462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74607, d85462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74608 q = 1) (hb : d77842 q = 1) : d85463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d85463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74608, d85463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74609 q = 1) (hb : d77842 q = 1) : d85464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d85464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74609, d85464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74610 q = 1) (hb : d77842 q = 1) : d85465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d85465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74610, d85465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74611 q = 1) (hb : d77842 q = 1) : d85466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d85466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74611, d85466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro14473 (p : Pattern) (ha : d487 p = 1) (hb : d77842 p = 1) : d7433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d485 q = 1) (hb : d77842 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d486 q = 1) (hb : d77842 q = 1) : d7432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d486, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d487 q = 1) (hb : d77842 q = 1) : d7433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d7433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d7433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14474 (p : Pattern) (ha : d497 p = 1) (hb : d77842 p = 1) : d7439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d77842 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d77842 q = 1) : d7434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14473 q ha hb
    | true =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d77842 q = 1) : d7435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d77842 q = 1) : d7436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d77842 q = 1) : d7437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d77842 q = 1) : d7438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d497 q = 1) (hb : d77842 q = 1) : d7439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d7439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d7439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14475 (p : Pattern) (ha : d500 p = 1) (hb : d77842 p = 1) : d7442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d485 q = 1) (hb : d77842 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d486 q = 1) (hb : d77842 q = 1) : d7432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d486, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d500 q = 1) (hb : d77842 q = 1) : d7442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d500, d7442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d500, d7442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14476 (p : Pattern) (ha : d507 p = 1) (hb : d77842 p = 1) : d7448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d77842 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d77842 q = 1) : d7434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14473 q ha hb
    | true =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d77842 q = 1) : d7435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d77842 q = 1) : d7436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d77842 q = 1) : d7437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d77842 q = 1) : d7438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d77842 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d502 q = 1) (hb : d77842 q = 1) : d7443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d7443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14475 q ha hb
    | true =>
      simp only [d502, d7443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d503 q = 1) (hb : d77842 q = 1) : d7444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d7444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d7444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d504 q = 1) (hb : d77842 q = 1) : d7445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d7445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d504, d7445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d505 q = 1) (hb : d77842 q = 1) : d7446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d7446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d7446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d506 q = 1) (hb : d77842 q = 1) : d7447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d7447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d7447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d507 q = 1) (hb : d77842 q = 1) : d7448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d7448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d507, d7448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14477 (p : Pattern) (ha : d638 p = 1) (hb : d77842 p = 1) : d7515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d77842 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d77842 q = 1) : d7434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14473 q ha hb
    | true =>
      simp only [d492, d7434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d77842 q = 1) : d7435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d7435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d77842 q = 1) : d7436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d7436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d77842 q = 1) : d7437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d7437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d77842 q = 1) : d7438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d7438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d77842 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d638 q = 1) (hb : d77842 q = 1) : d7515 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d7515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d638, d7515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14478 (p : Pattern) (ha : d512 p = 1) (hb : d77842 p = 1) : d7453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d485 q = 1) (hb : d77842 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d511 q = 1) (hb : d77842 q = 1) : d7452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d512 q = 1) (hb : d77842 q = 1) : d7453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d7453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d7453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14479 (p : Pattern) (ha : d521 p = 1) (hb : d77842 p = 1) : d7460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d519 q = 1) (hb : d77842 q = 1) : d7458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d520 q = 1) (hb : d77842 q = 1) : d7459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d521 q = 1) (hb : d77842 q = 1) : d7460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d7460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d7460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14480 (p : Pattern) (ha : d560 p = 1) (hb : d77842 p = 1) : d7471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d77842 q = 1) : d7468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d7468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d7468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d77842 q = 1) : d7469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d7469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d7469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d77842 q = 1) : d7470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d7470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d7470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d560 q = 1) (hb : d77842 q = 1) : d7471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d7471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d7471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14481 (p : Pattern) (ha : d5399 p = 1) (hb : d77842 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d77842 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d77842 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d77842 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5399 q = 1) (hb : d77842 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5399, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5399, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14482 (p : Pattern) (ha : d74615 p = 1) (hb : d77842 p = 1) : d85471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d77842 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d77842 q = 1) : d7454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14478 q ha hb
    | true =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d77842 q = 1) : d7455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d77842 q = 1) : d7456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d77842 q = 1) : d7457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d77842 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d77842 q = 1) : d7461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14479 q ha hb
    | true =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d77842 q = 1) : d7462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d77842 q = 1) : d7463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d561 q = 1) (hb : d77842 q = 1) : d7472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d7472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14480 q ha hb
    | true =>
      simp only [d561, d7472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14473 q ha hb
  have h11 (q : Pattern) (ha : d4408 q = 1) (hb : d77842 q = 1) : d85467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4408, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d77842 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14481 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d77842 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74612 q = 1) (hb : d77842 q = 1) : d85468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74612, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74613 q = 1) (hb : d77842 q = 1) : d85469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74613, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74614 q = 1) (hb : d77842 q = 1) : d85470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74614, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74615 q = 1) (hb : d77842 q = 1) : d85471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74615, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74615, d85471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14483 (p : Pattern) (ha : d609 p = 1) (hb : d77842 p = 1) : d7493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d485 q = 1) (hb : d77842 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d511 q = 1) (hb : d77842 q = 1) : d7452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d609 q = 1) (hb : d77842 q = 1) : d7493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, d7493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d609, d7493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14484 (p : Pattern) (ha : d615 p = 1) (hb : d77842 p = 1) : d7498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d484 q = 1) (hb : d77842 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d484, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d519 q = 1) (hb : d77842 q = 1) : d7458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d520 q = 1) (hb : d77842 q = 1) : d7459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d615 q = 1) (hb : d77842 q = 1) : d7498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, d7498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d615, d7498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14485 (p : Pattern) (ha : d620 p = 1) (hb : d77842 p = 1) : d7502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d557 q = 1) (hb : d77842 q = 1) : d7468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d7468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d557, d7468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d558 q = 1) (hb : d77842 q = 1) : d7469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d7469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d558, d7469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d559 q = 1) (hb : d77842 q = 1) : d7470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d7470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d559, d7470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d620 q = 1) (hb : d77842 q = 1) : d7502 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d620, d7502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d620, d7502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14486 (p : Pattern) (ha : d5406 p = 1) (hb : d77842 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5396 q = 1) (hb : d77842 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5397 q = 1) (hb : d77842 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5398 q = 1) (hb : d77842 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5406 q = 1) (hb : d77842 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14487 (p : Pattern) (ha : d74619 p = 1) (hb : d77842 p = 1) : d85476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d77842 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d77842 q = 1) : d7454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14478 q ha hb
    | true =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d77842 q = 1) : d7455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d77842 q = 1) : d7456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d77842 q = 1) : d7457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d77842 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d77842 q = 1) : d7461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14479 q ha hb
    | true =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d77842 q = 1) : d7462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d77842 q = 1) : d7463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d561 q = 1) (hb : d77842 q = 1) : d7472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d7472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14480 q ha hb
    | true =>
      simp only [d561, d7472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14473 q ha hb
  have h11 (q : Pattern) (ha : d4408 q = 1) (hb : d77842 q = 1) : d85467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4408, d85467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d77842 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14481 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d77842 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d74612 q = 1) (hb : d77842 q = 1) : d85468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74612, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74612, d85468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74613 q = 1) (hb : d77842 q = 1) : d85469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74613, d85469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74614 q = 1) (hb : d77842 q = 1) : d85470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74614, d85470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d77842 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d611 q = 1) (hb : d77842 q = 1) : d7494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d7494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14483 q ha hb
    | true =>
      simp only [d611, d7494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d612 q = 1) (hb : d77842 q = 1) : d7495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d7495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d7495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d613 q = 1) (hb : d77842 q = 1) : d7496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d7496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d613, d7496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d614 q = 1) (hb : d77842 q = 1) : d7497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d7497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d7497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d77842 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d617 q = 1) (hb : d77842 q = 1) : d7499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d7499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14484 q ha hb
    | true =>
      simp only [d617, d7499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d618 q = 1) (hb : d77842 q = 1) : d7500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d7500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d7500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d619 q = 1) (hb : d77842 q = 1) : d7501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d7501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d619, d7501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d621 q = 1) (hb : d77842 q = 1) : d7503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d7503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14485 q ha hb
    | true =>
      simp only [d621, d7503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14475 q ha hb
  have h27 (q : Pattern) (ha : d4413 q = 1) (hb : d77842 q = 1) : d85472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d4413, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5407 q = 1) (hb : d77842 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14486 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5408 q = 1) (hb : d77842 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d74616 q = 1) (hb : d77842 q = 1) : d85473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d74616, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74617 q = 1) (hb : d77842 q = 1) : d85474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74617, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74617, d85474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d74618 q = 1) (hb : d77842 q = 1) : d85475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74618, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74618, d85475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d74619 q = 1) (hb : d77842 q = 1) : d85476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74619, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74619, d85476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14488 (p : Pattern) (ha : d74626 p = 1) (hb : d77842 p = 1) : d85483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d621 q = 1) (hb : d77842 q = 1) : d7503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d7503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14485 q ha hb
    | true =>
      simp only [d621, d7503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14475 q ha hb
  have h2 (q : Pattern) (ha : d4413 q = 1) (hb : d77842 q = 1) : d85472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4413, d85472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d77842 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14486 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d77842 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74616 q = 1) (hb : d77842 q = 1) : d85473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74616, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74616, d85473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74624 q = 1) (hb : d77842 q = 1) : d85481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74624, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74624, d85481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74625 q = 1) (hb : d77842 q = 1) : d85482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74625, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74625, d85482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74626 q = 1) (hb : d77842 q = 1) : d85483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d85483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74626, d85483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14489 (p : Pattern) (ha : d681 p = 1) (hb : d77842 p = 1) : d7535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d77842 q = 1) : d7530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9845 q ha hb
    | true =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d77842 q = 1) : d7531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d678 q = 1) (hb : d77842 q = 1) : d7532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d678, d7532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d678, d7532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d679 q = 1) (hb : d77842 q = 1) : d7533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d679, d7533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d679, d7533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d680 q = 1) (hb : d77842 q = 1) : d7534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d680, d7534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d680, d7534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d681 q = 1) (hb : d77842 q = 1) : d7535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d681, d7535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d681, d7535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14490 (p : Pattern) (ha : d689 p = 1) (hb : d77842 p = 1) : d7539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d77842 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d686 q = 1) (hb : d77842 q = 1) : d7536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d687 q = 1) (hb : d77842 q = 1) : d7537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d687, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d688 q = 1) (hb : d77842 q = 1) : d7538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d688, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d689 q = 1) (hb : d77842 q = 1) : d7539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d689, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14491 (p : Pattern) (ha : d5428 p = 1) (hb : d77842 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5425 q = 1) (hb : d77842 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5426 q = 1) (hb : d77842 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5427 q = 1) (hb : d77842 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5428 q = 1) (hb : d77842 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14492 (p : Pattern) (ha : d74635 p = 1) (hb : d77842 p = 1) : d85493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d690 q = 1) (hb : d77842 q = 1) : d7540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d7540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14489 q ha hb
    | true =>
      simp only [d690, d7540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14490 q ha hb
  have h2 (q : Pattern) (ha : d4428 q = 1) (hb : d77842 q = 1) : d85489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d85489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4428, d85489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d77842 q = 1) : d7555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14491 q ha hb
    | true =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d77842 q = 1) : d7556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74632 q = 1) (hb : d77842 q = 1) : d85490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74632, d85490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74632, d85490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74633 q = 1) (hb : d77842 q = 1) : d85491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d85491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74633, d85491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74634 q = 1) (hb : d77842 q = 1) : d85492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d85492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74634, d85492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74635 q = 1) (hb : d77842 q = 1) : d85493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d85493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74635, d85493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14493 (p : Pattern) (ha : d74641 p = 1) (hb : d77842 p = 1) : d85499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d77842 q = 1) : d7440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d7440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d7440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14474 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d77842 q = 1) : d7441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d7441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d7441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d77842 q = 1) : d7449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14474 q ha hb
    | true =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14476 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d77842 q = 1) : d7450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d77842 q = 1) : d7451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d7451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d7451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74620 q = 1) (hb : d77842 q = 1) : d85477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74620, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14482 q ha hb
    | true =>
      simp only [d74620, d85477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14487 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d77842 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d645 q = 1) (hb : d77842 q = 1) : d7516 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d7516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14477 q ha hb
    | true =>
      simp only [d645, d7516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74621 q = 1) (hb : d77842 q = 1) : d85478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74621, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74621, d85478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74622 q = 1) (hb : d77842 q = 1) : d85479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d85479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74622, d85479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d74623 q = 1) (hb : d77842 q = 1) : d85480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d85480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74623, d85480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74627 q = 1) (hb : d77842 q = 1) : d85484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d85484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74627, d85484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14488 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d77842 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d74628 q = 1) (hb : d77842 q = 1) : d85485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d85485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74628, d85485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74629 q = 1) (hb : d77842 q = 1) : d85486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d85486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74629, d85486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74630 q = 1) (hb : d77842 q = 1) : d85487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d85487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74630, d85487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d74631 q = 1) (hb : d77842 q = 1) : d85488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d85488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74631, d85488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74636 q = 1) (hb : d77842 q = 1) : d85494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d85494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74636, d85494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14492 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d77842 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d74637 q = 1) (hb : d77842 q = 1) : d85495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d85495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74637, d85495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d74638 q = 1) (hb : d77842 q = 1) : d85496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d85496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74638, d85496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74639 q = 1) (hb : d77842 q = 1) : d85497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d85497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74639, d85497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74640 q = 1) (hb : d77842 q = 1) : d85498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d85498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74640, d85498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d74641 q = 1) (hb : d77842 q = 1) : d85499 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d85499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74641, d85499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14494 (p : Pattern) (ha : d74647 p = 1) (hb : d77842 p = 1) : d85505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74642 q = 1) (hb : d77842 q = 1) : d85500 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d85500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74642, d85500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14493 q ha hb
  have h2 (q : Pattern) (ha : d74643 q = 1) (hb : d77842 q = 1) : d85501 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d85501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74643, d85501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74644 q = 1) (hb : d77842 q = 1) : d85502 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d85502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74644, d85502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74645 q = 1) (hb : d77842 q = 1) : d85503 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d85503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74645, d85503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74646 q = 1) (hb : d77842 q = 1) : d85504 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d85504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74646, d85504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74647 q = 1) (hb : d77842 q = 1) : d85505 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d85505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74647, d85505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14495 (p : Pattern) (ha : d779 p = 1) (hb : d77842 p = 1) : d7581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d776 q = 1) (hb : d77842 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d777 q = 1) (hb : d77842 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d778 q = 1) (hb : d77842 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d779 q = 1) (hb : d77842 q = 1) : d7581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14496 (p : Pattern) (ha : d789 p = 1) (hb : d77842 p = 1) : d7587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d77842 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d77842 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14495 q ha hb
    | true =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d77842 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d77842 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d77842 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d77842 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d789 q = 1) (hb : d77842 q = 1) : d7587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d7587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d7587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14497 (p : Pattern) (ha : d792 p = 1) (hb : d77842 p = 1) : d7590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d776 q = 1) (hb : d77842 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d777 q = 1) (hb : d77842 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d778 q = 1) (hb : d77842 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d792 q = 1) (hb : d77842 q = 1) : d7590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d792, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14498 (p : Pattern) (ha : d799 p = 1) (hb : d77842 p = 1) : d7596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d77842 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d77842 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14495 q ha hb
    | true =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d77842 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d77842 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d77842 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d77842 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d77842 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d794 q = 1) (hb : d77842 q = 1) : d7591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14497 q ha hb
    | true =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d795 q = 1) (hb : d77842 q = 1) : d7592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d796 q = 1) (hb : d77842 q = 1) : d7593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d797 q = 1) (hb : d77842 q = 1) : d7594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d798 q = 1) (hb : d77842 q = 1) : d7595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d799 q = 1) (hb : d77842 q = 1) : d7596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d7596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d799, d7596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14499 (p : Pattern) (ha : d944 p = 1) (hb : d77842 p = 1) : d7663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d77842 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d77842 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14495 q ha hb
    | true =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d77842 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d77842 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d77842 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d77842 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d77842 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d944 q = 1) (hb : d77842 q = 1) : d7663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d7663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d944, d7663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
