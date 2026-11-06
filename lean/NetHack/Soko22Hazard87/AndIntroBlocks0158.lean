import NetHack.Soko22Hazard87.AndIntroBlocks0157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro39500 (p : Pattern) (ha : d16114 p = 1) (hb : d129471 p = 1) : d14312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d129471 q = 1) : d14309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d129471 q = 1) : d14310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d129471 q = 1) : d14311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d129471 q = 1) : d14312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39501 (p : Pattern) (ha : d128234 p = 1) (hb : d129471 p = 1) : d125494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d129471 q = 1) : d14248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39494 q ha hb
    | true =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39492 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d129471 q = 1) : d14249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d129471 q = 1) : d14250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d129471 q = 1) : d14251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d129471 q = 1) : d14258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39495 q ha hb
    | true =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39493 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d129471 q = 1) : d14259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d129471 q = 1) : d14260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d129471 q = 1) : d14280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39499 q ha hb
    | true =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39487 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d129471 q = 1) : d125490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d129471 q = 1) : d14313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39500 q ha hb
    | true =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d129471 q = 1) : d14314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d129471 q = 1) : d125491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d129471 q = 1) : d125492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d129471 q = 1) : d125493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d129471 q = 1) : d125494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39502 (p : Pattern) (ha : d610 p = 1) (hb : d129471 p = 1) : d14320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d129471 q = 1) : d14222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d129471 q = 1) : d14246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d129471 q = 1) : d14320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39503 (p : Pattern) (ha : d616 p = 1) (hb : d129471 p = 1) : d14326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d129471 q = 1) : d14221 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d129471 q = 1) : d14255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d129471 q = 1) : d14256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d129471 q = 1) : d14326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39504 (p : Pattern) (ha : d16121 p = 1) (hb : d129471 p = 1) : d14319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d129471 q = 1) : d14218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d129471 q = 1) : d14244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d129471 q = 1) : d14319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39505 (p : Pattern) (ha : d16126 p = 1) (hb : d129471 p = 1) : d14325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d129471 q = 1) : d14215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39478 q ha hb
    | true =>
      simp only [d482, d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d129471 q = 1) : d14216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d129471 q = 1) : d14217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d129471 q = 1) : d14252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d129471 q = 1) : d14253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d129471 q = 1) : d14325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39506 (p : Pattern) (ha : d16130 p = 1) (hb : d129471 p = 1) : d14330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d129471 q = 1) : d14274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39498 q ha hb
    | true =>
      simp only [d16088, d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d129471 q = 1) : d14275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d129471 q = 1) : d14276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d129471 q = 1) : d14277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d129471 q = 1) : d14278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d129471 q = 1) : d14330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39507 (p : Pattern) (ha : d16135 p = 1) (hb : d129471 p = 1) : d14336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d129471 q = 1) : d14211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39486 q ha hb
    | true =>
      simp only [d16037, d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d129471 q = 1) : d14212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d129471 q = 1) : d14309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d129471 q = 1) : d14310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d129471 q = 1) : d14311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d129471 q = 1) : d14336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39508 (p : Pattern) (ha : d128239 p = 1) (hb : d129471 p = 1) : d125499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d129471 q = 1) : d14248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39494 q ha hb
    | true =>
      simp only [d16063, d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39492 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d129471 q = 1) : d14249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d129471 q = 1) : d14250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d129471 q = 1) : d14251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d129471 q = 1) : d14258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39495 q ha hb
    | true =>
      simp only [d16070, d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39493 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d129471 q = 1) : d14259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d129471 q = 1) : d14260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d129471 q = 1) : d14280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39499 q ha hb
    | true =>
      simp only [d16094, d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39487 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d129471 q = 1) : d125490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d129471 q = 1) : d14313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39500 q ha hb
    | true =>
      simp only [d16115, d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d129471 q = 1) : d14314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d129471 q = 1) : d125491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d129471 q = 1) : d125492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d129471 q = 1) : d125493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d129471 q = 1) : d14321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39504 q ha hb
    | true =>
      simp only [d16122, d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39502 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d129471 q = 1) : d14322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d129471 q = 1) : d14323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d129471 q = 1) : d14324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d129471 q = 1) : d14327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39505 q ha hb
    | true =>
      simp only [d16127, d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39503 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d129471 q = 1) : d14328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d129471 q = 1) : d14329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d129471 q = 1) : d14331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39506 q ha hb
    | true =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39489 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d129471 q = 1) : d125495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d129471 q = 1) : d14337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39507 q ha hb
    | true =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d129471 q = 1) : d14338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d129471 q = 1) : d125496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d129471 q = 1) : d125497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d129471 q = 1) : d125498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d129471 q = 1) : d125499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro39509 (p : Pattern) (ha : d128246 p = 1) (hb : d129471 p = 1) : d125506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d129471 q = 1) : d14331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39506 q ha hb
    | true =>
      simp only [d16131, d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39489 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d129471 q = 1) : d125495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d129471 q = 1) : d14337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39507 q ha hb
    | true =>
      simp only [d16136, d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d129471 q = 1) : d14338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d129471 q = 1) : d125496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d129471 q = 1) : d125504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d129471 q = 1) : d125505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d129471 q = 1) : d125506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39510 (p : Pattern) (ha : d16162 p = 1) (hb : d129471 p = 1) : d14372 p = 1 := by
  have h0 (q : Pattern) (ha : d662 q = 1) (hb : d100904 q = 1) : d662 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d129471 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d129471, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16160, d129471, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12861 q = 1) (hb : d100904 q = 1) : d12861 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12602 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16161 q = 1) (hb : d129471 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16161, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16162 q = 1) (hb : d129471 q = 1) : d14372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16162, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39511 (p : Pattern) (ha : d16166 p = 1) (hb : d129471 p = 1) : d14376 p = 1 := by
  have h0 (q : Pattern) (ha : d12602 q = 1) (hb : d100904 q = 1) : d12602 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12603 q = 1) (hb : d129471 q = 1) : d14155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d129471, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12603, d129471, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d129471 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16166 q = 1) (hb : d129471 q = 1) : d14376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16166, d14376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39512 (p : Pattern) (ha : d16172 p = 1) (hb : d129471 p = 1) : d14382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d129471 q = 1) : d14373 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39510 q ha hb
    | true =>
      simp only [d16163, d14373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39472 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d129471 q = 1) : d14374 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d14374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d129471 q = 1) : d14375 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d14375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d129471 q = 1) : d14377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39472 q ha hb
    | true =>
      simp only [d16167, d14377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39511 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d129471 q = 1) : d14378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d14378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d129471 q = 1) : d14379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d14379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d129471 q = 1) : d14380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d129471 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39472 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d129471 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d129471 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d129471 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d129471 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d129471 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d129471 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d129471 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d129471 q = 1) : d14381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d129471 q = 1) : d14382 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39513 (p : Pattern) (ha : d16176 p = 1) (hb : d129471 p = 1) : d14387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d129471 q = 1) : d14157 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39472 q ha hb
    | true =>
      simp only [d16005, d14157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d129471 q = 1) : d14158 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d14158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d129471 q = 1) : d14159 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d14159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d129471 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d129471 q = 1) : d14021 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39447 q ha hb
    | true =>
      simp only [d232, d14021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d129471 q = 1) : d14022 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d14022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d129471 q = 1) : d14023 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d14023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d129471 q = 1) : d14160 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d129471 q = 1) : d14385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d129471 q = 1) : d14386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d129471 q = 1) : d14387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39514 (p : Pattern) (ha : d16182 p = 1) (hb : d129471 p = 1) : d14393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d129471 q = 1) : d14383 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39512 q ha hb
    | true =>
      simp only [d16173, d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d129471 q = 1) : d14384 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d129471 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39513 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d129471 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d129471 q = 1) : d14390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d129471 q = 1) : d14391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d129471 q = 1) : d14392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d129471 q = 1) : d14393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39515 (p : Pattern) (ha : d16186 p = 1) (hb : d129471 p = 1) : d14401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d129471 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39513 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d129471 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d129471 q = 1) : d14396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39483 q ha hb
    | true =>
      simp only [d684, d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d129471 q = 1) : d14397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d129471 q = 1) : d14398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d129471 q = 1) : d14399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d129471 q = 1) : d14400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d129471 q = 1) : d14401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39516 (p : Pattern) (ha : d16207 p = 1) (hb : d129471 p = 1) : d14436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d129471 q = 1) : d14388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39513 q ha hb
    | true =>
      simp only [d16177, d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d129471 q = 1) : d14389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d129471 q = 1) : d14433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d129471 q = 1) : d14434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d129471 q = 1) : d14435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d129471 q = 1) : d14436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39517 (p : Pattern) (ha : d128256 p = 1) (hb : d129471 p = 1) : d125516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d129471 q = 1) : d14402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39514 q ha hb
    | true =>
      simp only [d16187, d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39515 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d129471 q = 1) : d125512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d129471 q = 1) : d14437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39516 q ha hb
    | true =>
      simp only [d16208, d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d129471 q = 1) : d14438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d129471 q = 1) : d125513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d129471 q = 1) : d125514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d129471 q = 1) : d125515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d129471 q = 1) : d125516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39518 (p : Pattern) (ha : d128262 p = 1) (hb : d129471 p = 1) : d125522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d129471 q = 1) : d14231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39488 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d129471 q = 1) : d14232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d129471 q = 1) : d14241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39488 q ha hb
    | true =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39490 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d129471 q = 1) : d14242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d129471 q = 1) : d14243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d129471 q = 1) : d125500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39501 q ha hb
    | true =>
      simp only [d128240, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39508 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d129471 q = 1) : d14356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39491 q ha hb
    | true =>
      simp only [d16144, d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39481 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d129471 q = 1) : d125501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d129471 q = 1) : d125502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d129471 q = 1) : d125503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d129471 q = 1) : d125507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39509 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d129471 q = 1) : d14365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39482 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d129471 q = 1) : d125508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d129471 q = 1) : d125509 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d129471 q = 1) : d125510 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d129471 q = 1) : d125511 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d129471 q = 1) : d125517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39517 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d129471 q = 1) : d14454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39485 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d129471 q = 1) : d125518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d129471 q = 1) : d125519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d129471 q = 1) : d125520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d129471 q = 1) : d125521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d129471 q = 1) : d125522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39519 (p : Pattern) (ha : d128268 p = 1) (hb : d129471 p = 1) : d125528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d129471 q = 1) : d125523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39518 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d129471 q = 1) : d125524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d129471 q = 1) : d125525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d129471 q = 1) : d125526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d129471 q = 1) : d125527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d129471 q = 1) : d125528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39520 (p : Pattern) (ha : d758 p = 1) (hb : d129471 p = 1) : d14467 p = 1 := by
  have h0 (q : Pattern) (ha : d322 q = 1) (hb : d100904 q = 1) : d322 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d129471 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d129471, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d755, d129471, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d129471 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d758 q = 1) (hb : d129471 q = 1) : d14467 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d758, d14467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39521 (p : Pattern) (ha : d773 p = 1) (hb : d129471 p = 1) : d14481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d129471 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d129471 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39520 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d129471 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d129471 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d767 q = 1) (hb : d129471 q = 1) : d14475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d772 q = 1) (hb : d129471 q = 1) : d14480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d772, d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d773 q = 1) (hb : d129471 q = 1) : d14481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d773, d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39522 (p : Pattern) (ha : d783 p = 1) (hb : d129471 p = 1) : d14491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d129471 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d129471 q = 1) : d14490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d129471 q = 1) : d14491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39523 (p : Pattern) (ha : d793 p = 1) (hb : d129471 p = 1) : d14501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d129471 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d129471 q = 1) : d14490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d129471 q = 1) : d14501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39524 (p : Pattern) (ha : d950 p = 1) (hb : d129471 p = 1) : d14628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d129471 q = 1) : d14617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39522 q ha hb
    | true =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d129471 q = 1) : d14618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d129471 q = 1) : d14619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d129471 q = 1) : d14620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d129471 q = 1) : d14621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d129471 q = 1) : d14623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39523 q ha hb
    | true =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d129471 q = 1) : d14624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d129471 q = 1) : d14625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d129471 q = 1) : d14626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d129471 q = 1) : d14627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d129471 q = 1) : d14628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39525 (p : Pattern) (ha : d959 p = 1) (hb : d129471 p = 1) : d14637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d129471 q = 1) : d14623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39523 q ha hb
    | true =>
      simp only [d945, d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d129471 q = 1) : d14624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d129471 q = 1) : d14625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d129471 q = 1) : d14626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d129471 q = 1) : d14627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d129471 q = 1) : d14637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39526 (p : Pattern) (ha : d981 p = 1) (hb : d129471 p = 1) : d14658 p = 1 := by
  have h0 (q : Pattern) (ha : d415 q = 1) (hb : d100904 q = 1) : d415 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d129471 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d129471, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d975, d129471, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d129471 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d981 q = 1) (hb : d129471 q = 1) : d14658 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d981, d14658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39527 (p : Pattern) (ha : d1005 p = 1) (hb : d129471 p = 1) : d14680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d129471 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d129471 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39526 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d129471 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d129471 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d129471 q = 1) : d14670 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d129471 q = 1) : d14679 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1005 q = 1) (hb : d129471 q = 1) : d14680 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1005, d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39528 (p : Pattern) (ha : d1063 p = 1) (hb : d129471 p = 1) : d14736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d129471 q = 1) : d14681 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39527 q ha hb
    | true =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d129471 q = 1) : d14682 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d129471 q = 1) : d14733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d129471 q = 1) : d14734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d129471 q = 1) : d14735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d129471 q = 1) : d14736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39529 (p : Pattern) (ha : d1069 p = 1) (hb : d129471 p = 1) : d14742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d129471 q = 1) : d14737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39528 q ha hb
    | true =>
      simp only [d1064, d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d129471 q = 1) : d14738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d129471 q = 1) : d14739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d129471 q = 1) : d14740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d129471 q = 1) : d14741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d129471 q = 1) : d14742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39530 (p : Pattern) (ha : d16227 p = 1) (hb : d129471 p = 1) : d14263 p = 1 := by
  have h0 (q : Pattern) (ha : d546 q = 1) (hb : d100904 q = 1) : d546 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d129471 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d129471, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16075, d129471, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12749 q = 1) (hb : d100904 q = 1) : d12749 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12750 q = 1) (hb : d129471 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12750, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16227 q = 1) (hb : d129471 q = 1) : d14263 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16227, d14263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39531 (p : Pattern) (ha : d16233 p = 1) (hb : d129471 p = 1) : d14477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d129471 q = 1) : d14468 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39530 q ha hb
    | true =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39520 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d129471 q = 1) : d14469 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d129471 q = 1) : d14470 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d129471 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d129471 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39520 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d764 q = 1) (hb : d129471 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d765 q = 1) (hb : d129471 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16231 q = 1) (hb : d129471 q = 1) : d14474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d767 q = 1) (hb : d129471 q = 1) : d14475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d767, d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16232 q = 1) (hb : d129471 q = 1) : d14476 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16232, d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16233 q = 1) (hb : d129471 q = 1) : d14477 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16233, d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39532 (p : Pattern) (ha : d16239 p = 1) (hb : d129471 p = 1) : d14487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d129471 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d129471 q = 1) : d14486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d129471 q = 1) : d14487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39533 (p : Pattern) (ha : d16245 p = 1) (hb : d129471 p = 1) : d14497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d129471 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39532 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39522 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d129471 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d129471 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d129471 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d129471 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d129471 q = 1) : d14497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39534 (p : Pattern) (ha : d16248 p = 1) (hb : d129471 p = 1) : d14500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d129471 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d129471 q = 1) : d14486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d129471 q = 1) : d14500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39535 (p : Pattern) (ha : d16254 p = 1) (hb : d129471 p = 1) : d14507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d129471 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39532 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39522 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d129471 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d129471 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d129471 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d129471 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d129471 q = 1) : d14502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39534 q ha hb
    | true =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39523 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d129471 q = 1) : d14503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d129471 q = 1) : d14504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d129471 q = 1) : d14505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d129471 q = 1) : d14506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d129471 q = 1) : d14507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39536 (p : Pattern) (ha : d16343 p = 1) (hb : d129471 p = 1) : d14622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d129471 q = 1) : d14492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39532 q ha hb
    | true =>
      simp only [d16240, d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39522 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d129471 q = 1) : d14493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d129471 q = 1) : d14494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d129471 q = 1) : d14495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d129471 q = 1) : d14496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d129471 q = 1) : d14617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39522 q ha hb
    | true =>
      simp only [d939, d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d129471 q = 1) : d14618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d129471 q = 1) : d14619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d129471 q = 1) : d14620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d129471 q = 1) : d14621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d129471 q = 1) : d14622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39537 (p : Pattern) (ha : d806 p = 1) (hb : d129471 p = 1) : d14514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d129471 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d129471 q = 1) : d14513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d129471 q = 1) : d14514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39538 (p : Pattern) (ha : d816 p = 1) (hb : d129471 p = 1) : d14524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d129471 q = 1) : d14522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d129471 q = 1) : d14523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d129471 q = 1) : d14524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39539 (p : Pattern) (ha : d16259 p = 1) (hb : d129471 p = 1) : d14512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d129471 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d129471 q = 1) : d14511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d129471 q = 1) : d14512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39540 (p : Pattern) (ha : d16266 p = 1) (hb : d129471 p = 1) : d14521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d129471 q = 1) : d14519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d129471 q = 1) : d14520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d129471 q = 1) : d14521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39541 (p : Pattern) (ha : d16274 p = 1) (hb : d129471 p = 1) : d14532 p = 1 := by
  have h0 (q : Pattern) (ha : d837 q = 1) (hb : d100904 q = 1) : d837 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16271 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16272 q = 1) (hb : d129471 q = 1) : d14528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d129471, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16272, d129471, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14530 q = 1) (hb : d100904 q = 1) : d14530 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12749 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16273 q = 1) (hb : d129471 q = 1) : d14531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d129471, d14531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16273, d129471, d14531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16274 q = 1) (hb : d129471 q = 1) : d14532 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16274, d14532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39542 (p : Pattern) (ha : d16278 p = 1) (hb : d129471 p = 1) : d14536 p = 1 := by
  have h0 (q : Pattern) (ha : d12749 q = 1) (hb : d100904 q = 1) : d12749 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12750 q = 1) (hb : d129471 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12750, d129471, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d129471 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16278 q = 1) (hb : d129471 q = 1) : d14536 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16278, d14536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39543 (p : Pattern) (ha : d16284 p = 1) (hb : d129471 p = 1) : d14542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d129471 q = 1) : d14533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39541 q ha hb
    | true =>
      simp only [d16275, d14533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39530 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d129471 q = 1) : d14534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d14534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d129471 q = 1) : d14535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d14535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d129471 q = 1) : d14537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39530 q ha hb
    | true =>
      simp only [d16279, d14537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39542 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d129471 q = 1) : d14538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d14538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d129471 q = 1) : d14539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d14539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d129471 q = 1) : d14540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d129471 q = 1) : d14468 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39530 q ha hb
    | true =>
      simp only [d16228, d14468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39520 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d129471 q = 1) : d14469 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d14469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d129471 q = 1) : d14470 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d14470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d129471 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d129471 q = 1) : d14471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39520 q ha hb
    | true =>
      simp only [d763, d14471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d764 q = 1) (hb : d129471 q = 1) : d14472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d14472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d765 q = 1) (hb : d129471 q = 1) : d14473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d14473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16231 q = 1) (hb : d129471 q = 1) : d14474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16283 q = 1) (hb : d129471 q = 1) : d14541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16284 q = 1) (hb : d129471 q = 1) : d14542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16284, d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39544 (p : Pattern) (ha : d16290 p = 1) (hb : d129471 p = 1) : d14548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d129471 q = 1) : d14543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39543 q ha hb
    | true =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d129471 q = 1) : d14544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d129471 q = 1) : d14545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d129471 q = 1) : d14546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d129471 q = 1) : d14547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d129471 q = 1) : d14548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39545 (p : Pattern) (ha : d16314 p = 1) (hb : d129471 p = 1) : d14585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d129471 q = 1) : d14582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d129471 q = 1) : d14583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d129471 q = 1) : d14584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d129471 q = 1) : d14585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39546 (p : Pattern) (ha : d128274 p = 1) (hb : d129471 p = 1) : d125534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d129471 q = 1) : d14515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39539 q ha hb
    | true =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39537 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d129471 q = 1) : d14516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d129471 q = 1) : d14517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d129471 q = 1) : d14518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d129471 q = 1) : d14525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39540 q ha hb
    | true =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39538 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d129471 q = 1) : d14526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d129471 q = 1) : d14527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d129471 q = 1) : d14549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39544 q ha hb
    | true =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39532 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d129471 q = 1) : d125530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d129471 q = 1) : d14586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39545 q ha hb
    | true =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d129471 q = 1) : d14587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d129471 q = 1) : d125531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d129471 q = 1) : d125532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d129471 q = 1) : d125533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d129471 q = 1) : d125534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39547 (p : Pattern) (ha : d916 p = 1) (hb : d129471 p = 1) : d14593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d129471 q = 1) : d14489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d129471 q = 1) : d14513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d129471 q = 1) : d14593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39548 (p : Pattern) (ha : d922 p = 1) (hb : d129471 p = 1) : d14599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d129471 q = 1) : d14488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d129471 q = 1) : d14522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d129471 q = 1) : d14523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d129471 q = 1) : d14599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39549 (p : Pattern) (ha : d16321 p = 1) (hb : d129471 p = 1) : d14592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d129471 q = 1) : d14485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d129471 q = 1) : d14511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d129471 q = 1) : d14592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39550 (p : Pattern) (ha : d16326 p = 1) (hb : d129471 p = 1) : d14598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d129471 q = 1) : d14482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39521 q ha hb
    | true =>
      simp only [d774, d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d129471 q = 1) : d14483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d129471 q = 1) : d14484 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d129471 q = 1) : d14519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d129471 q = 1) : d14520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d129471 q = 1) : d14598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39551 (p : Pattern) (ha : d16330 p = 1) (hb : d129471 p = 1) : d14603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d129471 q = 1) : d14543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39543 q ha hb
    | true =>
      simp only [d16285, d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d129471 q = 1) : d14544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d129471 q = 1) : d14545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d129471 q = 1) : d14546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d129471 q = 1) : d14547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d129471 q = 1) : d14603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39552 (p : Pattern) (ha : d16335 p = 1) (hb : d129471 p = 1) : d14609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d129471 q = 1) : d14478 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39531 q ha hb
    | true =>
      simp only [d16234, d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d129471 q = 1) : d14479 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d129471 q = 1) : d14582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d129471 q = 1) : d14583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d129471 q = 1) : d14584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d129471 q = 1) : d14609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39553 (p : Pattern) (ha : d128279 p = 1) (hb : d129471 p = 1) : d125539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d129471 q = 1) : d14515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39539 q ha hb
    | true =>
      simp only [d16260, d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39537 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d129471 q = 1) : d14516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d129471 q = 1) : d14517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d129471 q = 1) : d14518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d129471 q = 1) : d14525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39540 q ha hb
    | true =>
      simp only [d16267, d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39538 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d129471 q = 1) : d14526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d129471 q = 1) : d14527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d129471 q = 1) : d14549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39544 q ha hb
    | true =>
      simp only [d16291, d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39532 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d129471 q = 1) : d125530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d129471 q = 1) : d14586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39545 q ha hb
    | true =>
      simp only [d16315, d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d129471 q = 1) : d14587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d129471 q = 1) : d125531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d129471 q = 1) : d125532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d129471 q = 1) : d125533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d129471 q = 1) : d14594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39549 q ha hb
    | true =>
      simp only [d16322, d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39547 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d129471 q = 1) : d14595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d129471 q = 1) : d14596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d129471 q = 1) : d14597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d129471 q = 1) : d14600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39550 q ha hb
    | true =>
      simp only [d16327, d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39548 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d129471 q = 1) : d14601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d129471 q = 1) : d14602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d129471 q = 1) : d14604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39551 q ha hb
    | true =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39534 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d129471 q = 1) : d125535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d129471 q = 1) : d14610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39552 q ha hb
    | true =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d129471 q = 1) : d14611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d129471 q = 1) : d125536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d129471 q = 1) : d125537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d129471 q = 1) : d125538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d129471 q = 1) : d125539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro39554 (p : Pattern) (ha : d128286 p = 1) (hb : d129471 p = 1) : d125546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d129471 q = 1) : d14604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39551 q ha hb
    | true =>
      simp only [d16331, d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39534 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d129471 q = 1) : d125535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d129471 q = 1) : d14610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39552 q ha hb
    | true =>
      simp only [d16336, d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d129471 q = 1) : d14611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d129471 q = 1) : d125536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d129471 q = 1) : d125544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d129471 q = 1) : d125545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d129471 q = 1) : d125546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39555 (p : Pattern) (ha : d16362 p = 1) (hb : d129471 p = 1) : d14649 p = 1 := by
  have h0 (q : Pattern) (ha : d968 q = 1) (hb : d100904 q = 1) : d968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16360 q = 1) (hb : d129471 q = 1) : d14643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d129471, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16360, d129471, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14647 q = 1) (hb : d100904 q = 1) : d14647 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16361 q = 1) (hb : d129471 q = 1) : d14648 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d129471, d14648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16361, d129471, d14648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16362 q = 1) (hb : d129471 q = 1) : d14649 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16362, d14649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39556 (p : Pattern) (ha : d16363 p = 1) (hb : d129471 p = 1) : d14372 p = 1 := by
  have h0 (q : Pattern) (ha : d662 q = 1) (hb : d100904 q = 1) : d662 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d129471 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d129471, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16160, d129471, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12861 q = 1) (hb : d100904 q = 1) : d12861 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12862 q = 1) (hb : d129471 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12862, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16363 q = 1) (hb : d129471 q = 1) : d14372 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16363, d14372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39557 (p : Pattern) (ha : d16367 p = 1) (hb : d129471 p = 1) : d14653 p = 1 := by
  have h0 (q : Pattern) (ha : d12861 q = 1) (hb : d100904 q = 1) : d12861 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12862 q = 1) (hb : d129471 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12862, d129471, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d129471 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16367 q = 1) (hb : d129471 q = 1) : d14653 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16367, d14653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39558 (p : Pattern) (ha : d16377 p = 1) (hb : d129471 p = 1) : d14667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d129471 q = 1) : d14650 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39555 q ha hb
    | true =>
      simp only [d16364, d14650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39556 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d129471 q = 1) : d14651 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d14651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d129471 q = 1) : d14652 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d14652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d129471 q = 1) : d14654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39556 q ha hb
    | true =>
      simp only [d16368, d14654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39557 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d129471 q = 1) : d14655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d14655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d129471 q = 1) : d14656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d14656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d129471 q = 1) : d14657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d129471 q = 1) : d14659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39556 q ha hb
    | true =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39526 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d129471 q = 1) : d14660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d129471 q = 1) : d14661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d129471 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d987 q = 1) (hb : d129471 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39526 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d129471 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d129471 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d129471 q = 1) : d14665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d129471 q = 1) : d14666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16377 q = 1) (hb : d129471 q = 1) : d14667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16377, d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39559 (p : Pattern) (ha : d16381 p = 1) (hb : d129471 p = 1) : d14672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d129471 q = 1) : d14659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39556 q ha hb
    | true =>
      simp only [d16372, d14659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39526 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d129471 q = 1) : d14660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d14660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d129471 q = 1) : d14661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d14661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d129471 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d987 q = 1) (hb : d129471 q = 1) : d14662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39526 q ha hb
    | true =>
      simp only [d987, d14662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d129471 q = 1) : d14663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d14663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d129471 q = 1) : d14664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d14664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d129471 q = 1) : d14665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d129471 q = 1) : d14670 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d129471 q = 1) : d14671 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16381 q = 1) (hb : d129471 q = 1) : d14672 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16381, d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39560 (p : Pattern) (ha : d16387 p = 1) (hb : d129471 p = 1) : d14678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d129471 q = 1) : d14668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39558 q ha hb
    | true =>
      simp only [d16378, d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d129471 q = 1) : d14669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d129471 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39559 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d129471 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d129471 q = 1) : d14675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d129471 q = 1) : d14676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d129471 q = 1) : d14677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d129471 q = 1) : d14678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39561 (p : Pattern) (ha : d16391 p = 1) (hb : d129471 p = 1) : d14686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d129471 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39559 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d129471 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d129471 q = 1) : d14681 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39527 q ha hb
    | true =>
      simp only [d1006, d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d129471 q = 1) : d14682 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d129471 q = 1) : d14683 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d129471 q = 1) : d14684 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d129471 q = 1) : d14685 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d129471 q = 1) : d14686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39562 (p : Pattern) (ha : d16417 p = 1) (hb : d129471 p = 1) : d14725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d129471 q = 1) : d14673 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39559 q ha hb
    | true =>
      simp only [d16382, d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d129471 q = 1) : d14674 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d129471 q = 1) : d14722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d129471 q = 1) : d14723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d129471 q = 1) : d14724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d129471 q = 1) : d14725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39563 (p : Pattern) (ha : d128296 p = 1) (hb : d129471 p = 1) : d125556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d129471 q = 1) : d14687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39560 q ha hb
    | true =>
      simp only [d16392, d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39561 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d129471 q = 1) : d125552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d129471 q = 1) : d14726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39562 q ha hb
    | true =>
      simp only [d16418, d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d129471 q = 1) : d14727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d129471 q = 1) : d125553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d129471 q = 1) : d125554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d129471 q = 1) : d125555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d129471 q = 1) : d125556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39564 (p : Pattern) (ha : d128302 p = 1) (hb : d129471 p = 1) : d125562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d129471 q = 1) : d14498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39533 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d129471 q = 1) : d14499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d129471 q = 1) : d14508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39533 q ha hb
    | true =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39535 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d129471 q = 1) : d14509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d129471 q = 1) : d14510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d129471 q = 1) : d125540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39546 q ha hb
    | true =>
      simp only [d128280, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39553 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d129471 q = 1) : d14629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39536 q ha hb
    | true =>
      simp only [d16344, d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39524 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d129471 q = 1) : d125541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d129471 q = 1) : d125542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d129471 q = 1) : d125543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d129471 q = 1) : d125547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39554 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d129471 q = 1) : d14638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39525 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d129471 q = 1) : d125548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d129471 q = 1) : d125549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d129471 q = 1) : d125550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d129471 q = 1) : d125551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d129471 q = 1) : d125557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39563 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d129471 q = 1) : d14743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39529 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d129471 q = 1) : d125558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d129471 q = 1) : d125559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d129471 q = 1) : d125560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d129471 q = 1) : d125561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d129471 q = 1) : d125562 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39565 (p : Pattern) (ha : d128308 p = 1) (hb : d129471 p = 1) : d125568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d129471 q = 1) : d125563 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39564 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d129471 q = 1) : d125564 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d129471 q = 1) : d125565 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d129471 q = 1) : d125566 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d129471 q = 1) : d125567 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d129471 q = 1) : d125568 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39566 (p : Pattern) (ha : d16442 p = 1) (hb : d129471 p = 1) : d14761 p = 1 := by
  have h0 (q : Pattern) (ha : d1103 q = 1) (hb : d100904 q = 1) : d1103 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16440 q = 1) (hb : d129471 q = 1) : d14757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d129471, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16440, d129471, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14759 q = 1) (hb : d100904 q = 1) : d14759 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14764 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16441 q = 1) (hb : d129471 q = 1) : d14760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d129471, d14760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16441, d129471, d14760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16442 q = 1) (hb : d129471 q = 1) : d14761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16442, d14761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39567 (p : Pattern) (ha : d16443 p = 1) (hb : d129471 p = 1) : d14766 p = 1 := by
  have h0 (q : Pattern) (ha : d1113 q = 1) (hb : d100904 q = 1) : d1113 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d129471 q = 1) : d14762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d129471, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1125, d129471, d14762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14765 q = 1) (hb : d129471 q = 1) : d14765 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16443 q = 1) (hb : d129471 q = 1) : d14766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16443, d14766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39568 (p : Pattern) (ha : d16456 p = 1) (hb : d129471 p = 1) : d14784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d129471 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d129471 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d129471 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d129471 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d129471 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d129471 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d129471 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d129471 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14778 q = 1) (hb : d129471 q = 1) : d14778 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16451 q = 1) (hb : d129471 q = 1) : d14779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16452 q = 1) (hb : d129471 q = 1) : d14780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16453 q = 1) (hb : d129471 q = 1) : d14781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16454 q = 1) (hb : d129471 q = 1) : d14782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16455 q = 1) (hb : d129471 q = 1) : d14783 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16455, d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16456 q = 1) (hb : d129471 q = 1) : d14784 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16456, d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39569 (p : Pattern) (ha : d16460 p = 1) (hb : d129471 p = 1) : d14788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14778 q = 1) (hb : d129471 q = 1) : d14778 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16451 q = 1) (hb : d129471 q = 1) : d14779 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16451, d14779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16452 q = 1) (hb : d129471 q = 1) : d14780 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d14780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16453 q = 1) (hb : d129471 q = 1) : d14781 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d14781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16454 q = 1) (hb : d129471 q = 1) : d14782 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16454, d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16459 q = 1) (hb : d129471 q = 1) : d14787 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16459, d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16460 q = 1) (hb : d129471 q = 1) : d14788 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16460, d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39570 (p : Pattern) (ha : d16466 p = 1) (hb : d129471 p = 1) : d14794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d129471 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d129471 q = 1) : d14793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d129471 q = 1) : d14794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39571 (p : Pattern) (ha : d16470 p = 1) (hb : d129471 p = 1) : d14798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d129471 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d129471 q = 1) : d14797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d129471 q = 1) : d14798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39572 (p : Pattern) (ha : d16476 p = 1) (hb : d129471 p = 1) : d14804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d129471 q = 1) : d14799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39570 q ha hb
    | true =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39571 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d129471 q = 1) : d14800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d129471 q = 1) : d14801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d129471 q = 1) : d14802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d129471 q = 1) : d14803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d129471 q = 1) : d14804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39573 (p : Pattern) (ha : d16479 p = 1) (hb : d129471 p = 1) : d14807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d129471 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d129471 q = 1) : d14793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d129471 q = 1) : d14807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39574 (p : Pattern) (ha : d16480 p = 1) (hb : d129471 p = 1) : d14808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d129471 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d129471 q = 1) : d14797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d129471 q = 1) : d14808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39575 (p : Pattern) (ha : d16486 p = 1) (hb : d129471 p = 1) : d14814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d129471 q = 1) : d14799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39570 q ha hb
    | true =>
      simp only [d16471, d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39571 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d129471 q = 1) : d14800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d129471 q = 1) : d14801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d129471 q = 1) : d14802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d129471 q = 1) : d14803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d129471 q = 1) : d14809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39573 q ha hb
    | true =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39574 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d129471 q = 1) : d14810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d129471 q = 1) : d14811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d129471 q = 1) : d14812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d129471 q = 1) : d14813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d129471 q = 1) : d14814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39576 (p : Pattern) (ha : d16527 p = 1) (hb : d129471 p = 1) : d14855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d129471 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d129471 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d129471 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d129471 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d129471 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d129471 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d129471 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d129471 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16525 q = 1) (hb : d129471 q = 1) : d14853 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16525, d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16526 q = 1) (hb : d129471 q = 1) : d14854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16526, d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16527 q = 1) (hb : d129471 q = 1) : d14855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16527, d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39577 (p : Pattern) (ha : d16537 p = 1) (hb : d129471 p = 1) : d14865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d129471 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39576 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d129471 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d129471 q = 1) : d14862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d129471 q = 1) : d14863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d129471 q = 1) : d14864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d129471 q = 1) : d14865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39578 (p : Pattern) (ha : d16628 p = 1) (hb : d129471 p = 1) : d14965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d129471 q = 1) : d14955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39577 q ha hb
    | true =>
      simp only [d16618, d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39571 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d129471 q = 1) : d14956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d129471 q = 1) : d14957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d129471 q = 1) : d14958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d129471 q = 1) : d14959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d129471 q = 1) : d14960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39571 q ha hb
    | true =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d129471 q = 1) : d14961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d129471 q = 1) : d14962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d129471 q = 1) : d14963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d129471 q = 1) : d14964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d129471 q = 1) : d14965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39579 (p : Pattern) (ha : d16634 p = 1) (hb : d129471 p = 1) : d14971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d129471 q = 1) : d14960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39571 q ha hb
    | true =>
      simp only [d16623, d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d129471 q = 1) : d14961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d129471 q = 1) : d14962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d129471 q = 1) : d14963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d129471 q = 1) : d14964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d129471 q = 1) : d14966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39574 q ha hb
    | true =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d129471 q = 1) : d14967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d129471 q = 1) : d14968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d129471 q = 1) : d14969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d129471 q = 1) : d14970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d129471 q = 1) : d14971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39580 (p : Pattern) (ha : d16643 p = 1) (hb : d129471 p = 1) : d14980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d129471 q = 1) : d14966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39574 q ha hb
    | true =>
      simp only [d16629, d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d129471 q = 1) : d14967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d129471 q = 1) : d14968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d129471 q = 1) : d14969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d129471 q = 1) : d14970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d129471 q = 1) : d14980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39581 (p : Pattern) (ha : d16672 p = 1) (hb : d129471 p = 1) : d15015 p = 1 := by
  have h0 (q : Pattern) (ha : d1388 q = 1) (hb : d100904 q = 1) : d1388 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1395 q = 1) (hb : d129471 q = 1) : d15014 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d129471, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1395, d129471, d15014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15008 q = 1) (hb : d129471 q = 1) : d15008 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16672 q = 1) (hb : d129471 q = 1) : d15015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16672, d15015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39582 (p : Pattern) (ha : d16698 p = 1) (hb : d129471 p = 1) : d15048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15042 q = 1) (hb : d129471 q = 1) : d15042 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16693 q = 1) (hb : d129471 q = 1) : d15043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16694 q = 1) (hb : d129471 q = 1) : d15044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16695 q = 1) (hb : d129471 q = 1) : d15045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16696 q = 1) (hb : d129471 q = 1) : d15046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16697 q = 1) (hb : d129471 q = 1) : d15047 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16697, d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16698 q = 1) (hb : d129471 q = 1) : d15048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16698, d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39583 (p : Pattern) (ha : d16765 p = 1) (hb : d129471 p = 1) : d15128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d129471 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39582 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d129471 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d129471 q = 1) : d15125 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d129471 q = 1) : d15126 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d129471 q = 1) : d15127 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d129471 q = 1) : d15128 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39584 (p : Pattern) (ha : d16771 p = 1) (hb : d129471 p = 1) : d15134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d129471 q = 1) : d15129 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39583 q ha hb
    | true =>
      simp only [d16766, d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d129471 q = 1) : d15130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d129471 q = 1) : d15131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d129471 q = 1) : d15132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d129471 q = 1) : d15133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d129471 q = 1) : d15134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39585 (p : Pattern) (ha : d16491 p = 1) (hb : d129471 p = 1) : d14819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d129471 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d129471 q = 1) : d14818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d129471 q = 1) : d14819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39586 (p : Pattern) (ha : d16493 p = 1) (hb : d129471 p = 1) : d14821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d129471 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d129471 q = 1) : d14820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d129471 q = 1) : d14821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39587 (p : Pattern) (ha : d16500 p = 1) (hb : d129471 p = 1) : d14828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d129471 q = 1) : d14826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d129471 q = 1) : d14827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d129471 q = 1) : d14828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39588 (p : Pattern) (ha : d16503 p = 1) (hb : d129471 p = 1) : d14831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d129471 q = 1) : d14829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d129471 q = 1) : d14830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d129471 q = 1) : d14831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39589 (p : Pattern) (ha : d16511 p = 1) (hb : d129471 p = 1) : d14839 p = 1 := by
  have h0 (q : Pattern) (ha : d1213 q = 1) (hb : d100904 q = 1) : d1213 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16508 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16509 q = 1) (hb : d129471 q = 1) : d14835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d129471, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16509, d129471, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14837 q = 1) (hb : d100904 q = 1) : d14837 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14759 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16510 q = 1) (hb : d129471 q = 1) : d14838 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d129471, d14838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16510, d129471, d14838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16511 q = 1) (hb : d129471 q = 1) : d14839 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16511, d14839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39590 (p : Pattern) (ha : d16516 p = 1) (hb : d129471 p = 1) : d14844 p = 1 := by
  have h0 (q : Pattern) (ha : d13023 q = 1) (hb : d100904 q = 1) : d13023 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16515 q = 1) (hb : d129471 q = 1) : d14843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d129471, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16515, d129471, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14765 q = 1) (hb : d129471 q = 1) : d14765 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16516 q = 1) (hb : d129471 q = 1) : d14844 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16516, d14844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39591 (p : Pattern) (ha : d16522 p = 1) (hb : d129471 p = 1) : d14850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d129471 q = 1) : d14840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39589 q ha hb
    | true =>
      simp only [d16512, d14840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d129471 q = 1) : d14841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d14841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d129471 q = 1) : d14842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d14842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d129471 q = 1) : d14845 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
    | true =>
      simp only [d16517, d14845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39590 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d129471 q = 1) : d14846 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d14846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d129471 q = 1) : d14847 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d14847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d129471 q = 1) : d14848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d129471 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d129471 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d129471 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14773 q = 1) (hb : d129471 q = 1) : d14773 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16447 q = 1) (hb : d129471 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16448 q = 1) (hb : d129471 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16449 q = 1) (hb : d129471 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16450 q = 1) (hb : d129471 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16521 q = 1) (hb : d129471 q = 1) : d14849 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16522 q = 1) (hb : d129471 q = 1) : d14850 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16522, d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39592 (p : Pattern) (ha : d16533 p = 1) (hb : d129471 p = 1) : d14861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d129471 q = 1) : d14851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39591 q ha hb
    | true =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d129471 q = 1) : d14852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d129471 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39576 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d129471 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d129471 q = 1) : d14858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d129471 q = 1) : d14859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d129471 q = 1) : d14860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d129471 q = 1) : d14861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39593 (p : Pattern) (ha : d16579 p = 1) (hb : d129471 p = 1) : d14916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d129471 q = 1) : d14767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39566 q ha hb
    | true =>
      simp only [d16444, d14767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d129471 q = 1) : d14768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d14768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d129471 q = 1) : d14769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d14769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14773 q = 1) (hb : d129471 q = 1) : d14773 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16447 q = 1) (hb : d129471 q = 1) : d14774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16447, d14774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16448 q = 1) (hb : d129471 q = 1) : d14775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d14775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16449 q = 1) (hb : d129471 q = 1) : d14776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d14776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16450 q = 1) (hb : d129471 q = 1) : d14777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12961 q = 1) (hb : d129471 q = 1) : d12961 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16574 q = 1) (hb : d129471 q = 1) : d14911 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39567 q ha hb
    | true =>
      simp only [d16574, d14911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16575 q = 1) (hb : d129471 q = 1) : d14912 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d14912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16576 q = 1) (hb : d129471 q = 1) : d14913 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d14913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16577 q = 1) (hb : d129471 q = 1) : d14914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16577, d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16578 q = 1) (hb : d129471 q = 1) : d14915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16578, d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16579 q = 1) (hb : d129471 q = 1) : d14916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16579, d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39594 (p : Pattern) (ha : d16585 p = 1) (hb : d129471 p = 1) : d14922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d129471 q = 1) : d14917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39593 q ha hb
    | true =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d129471 q = 1) : d14918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d129471 q = 1) : d14919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d129471 q = 1) : d14920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d129471 q = 1) : d14921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d129471 q = 1) : d14922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39595 (p : Pattern) (ha : d128315 p = 1) (hb : d129471 p = 1) : d125575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d129471 q = 1) : d14822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39585 q ha hb
    | true =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39586 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d129471 q = 1) : d14823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d129471 q = 1) : d14824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d129471 q = 1) : d14825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d129471 q = 1) : d14832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39587 q ha hb
    | true =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39588 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d129471 q = 1) : d14833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d129471 q = 1) : d14834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d129471 q = 1) : d14866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39592 q ha hb
    | true =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39577 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d129471 q = 1) : d125571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d129471 q = 1) : d14923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39594 q ha hb
    | true =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d129471 q = 1) : d14924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d129471 q = 1) : d125572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d129471 q = 1) : d125573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d129471 q = 1) : d125574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128315 q = 1) (hb : d129471 q = 1) : d125575 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128315, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39596 (p : Pattern) (ha : d16592 p = 1) (hb : d129471 p = 1) : d14929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d129471 q = 1) : d14792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d129471 q = 1) : d14818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d129471 q = 1) : d14929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39597 (p : Pattern) (ha : d16593 p = 1) (hb : d129471 p = 1) : d14930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d129471 q = 1) : d14796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d129471 q = 1) : d14820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d129471 q = 1) : d14930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39598 (p : Pattern) (ha : d16598 p = 1) (hb : d129471 p = 1) : d14935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d129471 q = 1) : d14785 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39568 q ha hb
    | true =>
      simp only [d16457, d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d129471 q = 1) : d14786 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d129471 q = 1) : d14791 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d129471 q = 1) : d14826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d129471 q = 1) : d14827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d129471 q = 1) : d14935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39599 (p : Pattern) (ha : d16599 p = 1) (hb : d129471 p = 1) : d14936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d129471 q = 1) : d14795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d129471 q = 1) : d14829 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d129471 q = 1) : d14830 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d129471 q = 1) : d14936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39600 (p : Pattern) (ha : d16603 p = 1) (hb : d129471 p = 1) : d14940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d129471 q = 1) : d14851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39591 q ha hb
    | true =>
      simp only [d16523, d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d129471 q = 1) : d14852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d129471 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39576 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d129471 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d129471 q = 1) : d14858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d129471 q = 1) : d14859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d129471 q = 1) : d14860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d129471 q = 1) : d14940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39601 (p : Pattern) (ha : d16604 p = 1) (hb : d129471 p = 1) : d14941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d129471 q = 1) : d14856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39576 q ha hb
    | true =>
      simp only [d16528, d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d129471 q = 1) : d14857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d129471 q = 1) : d14789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39569 q ha hb
    | true =>
      simp only [d16461, d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d129471 q = 1) : d14790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d129471 q = 1) : d14862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d129471 q = 1) : d14863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d129471 q = 1) : d14864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d129471 q = 1) : d14941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39602 (p : Pattern) (ha : d16610 p = 1) (hb : d129471 p = 1) : d14947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d129471 q = 1) : d14917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39593 q ha hb
    | true =>
      simp only [d16580, d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d129471 q = 1) : d14918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d129471 q = 1) : d14919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d129471 q = 1) : d14920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d129471 q = 1) : d14921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d129471 q = 1) : d14947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39603 (p : Pattern) (ha : d128320 p = 1) (hb : d129471 p = 1) : d125580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d129471 q = 1) : d14822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39585 q ha hb
    | true =>
      simp only [d16494, d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39586 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d129471 q = 1) : d14823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d129471 q = 1) : d14824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d129471 q = 1) : d14825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d129471 q = 1) : d14832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39587 q ha hb
    | true =>
      simp only [d16504, d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39588 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d129471 q = 1) : d14833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d129471 q = 1) : d14834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d129471 q = 1) : d14866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39592 q ha hb
    | true =>
      simp only [d16538, d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39577 q ha hb
  have h9 (q : Pattern) (ha : d128311 q = 1) (hb : d129471 q = 1) : d125571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128311, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d129471 q = 1) : d14923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39594 q ha hb
    | true =>
      simp only [d16586, d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d129471 q = 1) : d14924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128312 q = 1) (hb : d129471 q = 1) : d125572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128313 q = 1) (hb : d129471 q = 1) : d125573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128313, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128314 q = 1) (hb : d129471 q = 1) : d125574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128314, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d129471 q = 1) : d14931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39596 q ha hb
    | true =>
      simp only [d16594, d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39597 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d129471 q = 1) : d14932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d129471 q = 1) : d14933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d129471 q = 1) : d14934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d129471 q = 1) : d14937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39598 q ha hb
    | true =>
      simp only [d16600, d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39599 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d129471 q = 1) : d14938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d129471 q = 1) : d14939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d129471 q = 1) : d14942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39600 q ha hb
    | true =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39601 q ha hb
  have h23 (q : Pattern) (ha : d128316 q = 1) (hb : d129471 q = 1) : d125576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d129471 q = 1) : d14948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39602 q ha hb
    | true =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d129471 q = 1) : d14949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128317 q = 1) (hb : d129471 q = 1) : d125577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128318 q = 1) (hb : d129471 q = 1) : d125578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128318, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128319 q = 1) (hb : d129471 q = 1) : d125579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128319, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128320 q = 1) (hb : d129471 q = 1) : d125580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro39604 (p : Pattern) (ha : d128327 p = 1) (hb : d129471 p = 1) : d125587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d129471 q = 1) : d14942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39600 q ha hb
    | true =>
      simp only [d16605, d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39601 q ha hb
  have h2 (q : Pattern) (ha : d128316 q = 1) (hb : d129471 q = 1) : d125576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128316, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d129471 q = 1) : d14948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39602 q ha hb
    | true =>
      simp only [d16611, d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d129471 q = 1) : d14949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128317 q = 1) (hb : d129471 q = 1) : d125577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128325 q = 1) (hb : d129471 q = 1) : d125585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128325, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128326 q = 1) (hb : d129471 q = 1) : d125586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128326, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d129471 q = 1) : d125587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39605 (p : Pattern) (ha : d16655 p = 1) (hb : d129471 p = 1) : d14992 p = 1 := by
  have h0 (q : Pattern) (ha : d1379 q = 1) (hb : d100904 q = 1) : d1379 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16653 q = 1) (hb : d129471 q = 1) : d14986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d129471, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16653, d129471, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14990 q = 1) (hb : d100904 q = 1) : d14990 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14997 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16654 q = 1) (hb : d129471 q = 1) : d14991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d129471, d14991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16654, d129471, d14991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16655 q = 1) (hb : d129471 q = 1) : d14992 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16655, d14992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39606 (p : Pattern) (ha : d16662 p = 1) (hb : d129471 p = 1) : d14999 p = 1 := by
  have h0 (q : Pattern) (ha : d1383 q = 1) (hb : d100904 q = 1) : d1383 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16660 q = 1) (hb : d129471 q = 1) : d14993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d129471, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16660, d129471, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14997 q = 1) (hb : d100904 q = 1) : d14997 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15007 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16661 q = 1) (hb : d129471 q = 1) : d14998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d129471, d14998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16661, d129471, d14998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16662 q = 1) (hb : d129471 q = 1) : d14999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16662, d14999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39607 (p : Pattern) (ha : d16667 p = 1) (hb : d129471 p = 1) : d15009 p = 1 := by
  have h0 (q : Pattern) (ha : d13163 q = 1) (hb : d100904 q = 1) : d13163 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16666 q = 1) (hb : d129471 q = 1) : d15003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d129471, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16666, d129471, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15008 q = 1) (hb : d129471 q = 1) : d15008 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16667 q = 1) (hb : d129471 q = 1) : d15009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16667, d15009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39608 (p : Pattern) (ha : d16681 p = 1) (hb : d129471 p = 1) : d15030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d129471 q = 1) : d15000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39605 q ha hb
    | true =>
      simp only [d16663, d15000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d129471 q = 1) : d15001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d15001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d129471 q = 1) : d15002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d15002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d129471 q = 1) : d15010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
    | true =>
      simp only [d16668, d15010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39607 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d129471 q = 1) : d15011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d15011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d129471 q = 1) : d15012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d15012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d129471 q = 1) : d15013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d129471 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d129471 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d129471 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15024 q = 1) (hb : d129471 q = 1) : d15024 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16676 q = 1) (hb : d129471 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16677 q = 1) (hb : d129471 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16678 q = 1) (hb : d129471 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16679 q = 1) (hb : d129471 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16680 q = 1) (hb : d129471 q = 1) : d15029 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16681 q = 1) (hb : d129471 q = 1) : d15030 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16681, d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39609 (p : Pattern) (ha : d16686 p = 1) (hb : d129471 p = 1) : d15035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d129471 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d129471 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d129471 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d129471 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d129471 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129471 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129471 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129471 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16684 q = 1) (hb : d129471 q = 1) : d15033 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16684, d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16685 q = 1) (hb : d129471 q = 1) : d15034 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16685, d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16686 q = 1) (hb : d129471 q = 1) : d15035 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16686, d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39610 (p : Pattern) (ha : d16692 p = 1) (hb : d129471 p = 1) : d15041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d129471 q = 1) : d15031 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39608 q ha hb
    | true =>
      simp only [d16682, d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d129471 q = 1) : d15032 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d129471 q = 1) : d15036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39609 q ha hb
    | true =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d129471 q = 1) : d15037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d129471 q = 1) : d15038 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d129471 q = 1) : d15039 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d129471 q = 1) : d15040 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d129471 q = 1) : d15041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39611 (p : Pattern) (ha : d16704 p = 1) (hb : d129471 p = 1) : d15054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d129471 q = 1) : d15036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39609 q ha hb
    | true =>
      simp only [d16687, d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d129471 q = 1) : d15037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d129471 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39582 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d129471 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d129471 q = 1) : d15051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d129471 q = 1) : d15052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d129471 q = 1) : d15053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d129471 q = 1) : d15054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39612 (p : Pattern) (ha : d16748 p = 1) (hb : d129471 p = 1) : d15111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d129471 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d129471 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d129471 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d129471 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d129471 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129471 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129471 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129471 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d129471 q = 1) : d13190 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16743 q = 1) (hb : d129471 q = 1) : d15106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16743, d15106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16744 q = 1) (hb : d129471 q = 1) : d15107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d15107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16745 q = 1) (hb : d129471 q = 1) : d15108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d15108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16746 q = 1) (hb : d129471 q = 1) : d15109 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16746, d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16747 q = 1) (hb : d129471 q = 1) : d15110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16747, d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16748 q = 1) (hb : d129471 q = 1) : d15111 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16748, d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39613 (p : Pattern) (ha : d16754 p = 1) (hb : d129471 p = 1) : d15117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d129471 q = 1) : d15112 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39612 q ha hb
    | true =>
      simp only [d16749, d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d129471 q = 1) : d15113 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d129471 q = 1) : d15114 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d129471 q = 1) : d15115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d129471 q = 1) : d15116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d129471 q = 1) : d15117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39614 (p : Pattern) (ha : d128337 p = 1) (hb : d129471 p = 1) : d125597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d129471 q = 1) : d15055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39610 q ha hb
    | true =>
      simp only [d16705, d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39611 q ha hb
  have h2 (q : Pattern) (ha : d128333 q = 1) (hb : d129471 q = 1) : d125593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128333, d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d129471 q = 1) : d15118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39613 q ha hb
    | true =>
      simp only [d16755, d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d129471 q = 1) : d15119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d129471 q = 1) : d125594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d129471 q = 1) : d125595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d129471 q = 1) : d125596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d129471 q = 1) : d125597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39615 (p : Pattern) (ha : d128343 p = 1) (hb : d129471 p = 1) : d125603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d129471 q = 1) : d14805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39572 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d129471 q = 1) : d14806 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d129471 q = 1) : d14815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39572 q ha hb
    | true =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39575 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d129471 q = 1) : d14816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d129471 q = 1) : d14817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128321 q = 1) (hb : d129471 q = 1) : d125581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39595 q ha hb
    | true =>
      simp only [d128321, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39603 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d129471 q = 1) : d14972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39578 q ha hb
    | true =>
      simp only [d16635, d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39579 q ha hb
  have h8 (q : Pattern) (ha : d128322 q = 1) (hb : d129471 q = 1) : d125582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128323 q = 1) (hb : d129471 q = 1) : d125583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128324 q = 1) (hb : d129471 q = 1) : d125584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128324, d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128328 q = 1) (hb : d129471 q = 1) : d125588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128328, d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39604 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d129471 q = 1) : d14981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39580 q ha hb
  have h13 (q : Pattern) (ha : d128329 q = 1) (hb : d129471 q = 1) : d125589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128330 q = 1) (hb : d129471 q = 1) : d125590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128331 q = 1) (hb : d129471 q = 1) : d125591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128332 q = 1) (hb : d129471 q = 1) : d125592 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128338 q = 1) (hb : d129471 q = 1) : d125598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128338, d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39614 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d129471 q = 1) : d15135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39584 q ha hb
  have h19 (q : Pattern) (ha : d128339 q = 1) (hb : d129471 q = 1) : d125599 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128340 q = 1) (hb : d129471 q = 1) : d125600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128341 q = 1) (hb : d129471 q = 1) : d125601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128342 q = 1) (hb : d129471 q = 1) : d125602 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128343 q = 1) (hb : d129471 q = 1) : d125603 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39616 (p : Pattern) (ha : d128349 p = 1) (hb : d129471 p = 1) : d125609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d129471 q = 1) : d125604 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39615 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d129471 q = 1) : d125605 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d129471 q = 1) : d125606 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d129471 q = 1) : d125607 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d129471 q = 1) : d125608 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d129471 q = 1) : d125609 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39617 (p : Pattern) (ha : d16791 p = 1) (hb : d129471 p = 1) : d15154 p = 1 := by
  have h0 (q : Pattern) (ha : d1558 q = 1) (hb : d100904 q = 1) : d1558 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16789 q = 1) (hb : d129471 q = 1) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d129471, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16789, d129471, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15152 q = 1) (hb : d100904 q = 1) : d15152 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16790 q = 1) (hb : d129471 q = 1) : d15153 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d129471, d15153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16790, d129471, d15153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16791 q = 1) (hb : d129471 q = 1) : d15154 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16791, d15154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39618 (p : Pattern) (ha : d16795 p = 1) (hb : d129471 p = 1) : d15159 p = 1 := by
  have h0 (q : Pattern) (ha : d1573 q = 1) (hb : d100904 q = 1) : d1573 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16794 q = 1) (hb : d129471 q = 1) : d15155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d129471, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16794, d129471, d15155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15158 q = 1) (hb : d129471 q = 1) : d15158 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16795 q = 1) (hb : d129471 q = 1) : d15159 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16795, d15159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39619 (p : Pattern) (ha : d16808 p = 1) (hb : d129471 p = 1) : d15177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d129471 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d129471 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d129471 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d129471 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d129471 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d129471 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d129471 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d129471 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15171 q = 1) (hb : d129471 q = 1) : d15171 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16803 q = 1) (hb : d129471 q = 1) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16804 q = 1) (hb : d129471 q = 1) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16805 q = 1) (hb : d129471 q = 1) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16806 q = 1) (hb : d129471 q = 1) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16807 q = 1) (hb : d129471 q = 1) : d15176 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16807, d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16808 q = 1) (hb : d129471 q = 1) : d15177 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16808, d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39620 (p : Pattern) (ha : d16812 p = 1) (hb : d129471 p = 1) : d15181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15171 q = 1) (hb : d129471 q = 1) : d15171 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16803 q = 1) (hb : d129471 q = 1) : d15172 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16803, d15172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16804 q = 1) (hb : d129471 q = 1) : d15173 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d15173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16805 q = 1) (hb : d129471 q = 1) : d15174 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d15174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16806 q = 1) (hb : d129471 q = 1) : d15175 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16806, d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16811 q = 1) (hb : d129471 q = 1) : d15180 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16811, d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16812 q = 1) (hb : d129471 q = 1) : d15181 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16812, d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39621 (p : Pattern) (ha : d16818 p = 1) (hb : d129471 p = 1) : d15187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d129471 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d129471 q = 1) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d129471 q = 1) : d15187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39622 (p : Pattern) (ha : d16822 p = 1) (hb : d129471 p = 1) : d15191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d129471 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d129471 q = 1) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d129471 q = 1) : d15191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39623 (p : Pattern) (ha : d16828 p = 1) (hb : d129471 p = 1) : d15197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d129471 q = 1) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39621 q ha hb
    | true =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39622 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d129471 q = 1) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d129471 q = 1) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d129471 q = 1) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d129471 q = 1) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d129471 q = 1) : d15197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39624 (p : Pattern) (ha : d16831 p = 1) (hb : d129471 p = 1) : d15200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d129471 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d129471 q = 1) : d15186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d129471 q = 1) : d15200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39625 (p : Pattern) (ha : d16832 p = 1) (hb : d129471 p = 1) : d15201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d129471 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d129471 q = 1) : d15190 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d129471 q = 1) : d15201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39626 (p : Pattern) (ha : d16838 p = 1) (hb : d129471 p = 1) : d15207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d129471 q = 1) : d15192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39621 q ha hb
    | true =>
      simp only [d16823, d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39622 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d129471 q = 1) : d15193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d129471 q = 1) : d15194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d129471 q = 1) : d15195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d129471 q = 1) : d15196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d129471 q = 1) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39624 q ha hb
    | true =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39625 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d129471 q = 1) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d129471 q = 1) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d129471 q = 1) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d129471 q = 1) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d129471 q = 1) : d15207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39627 (p : Pattern) (ha : d16879 p = 1) (hb : d129471 p = 1) : d15248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d129471 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d129471 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d129471 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d129471 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d129471 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d129471 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d129471 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d129471 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d16877 q = 1) (hb : d129471 q = 1) : d15246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16877, d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16878 q = 1) (hb : d129471 q = 1) : d15247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16878, d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16879 q = 1) (hb : d129471 q = 1) : d15248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16879, d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39628 (p : Pattern) (ha : d16889 p = 1) (hb : d129471 p = 1) : d15258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d129471 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39627 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d129471 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d129471 q = 1) : d15255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d129471 q = 1) : d15256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d129471 q = 1) : d15257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d129471 q = 1) : d15258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39629 (p : Pattern) (ha : d16983 p = 1) (hb : d129471 p = 1) : d15358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d129471 q = 1) : d15348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39628 q ha hb
    | true =>
      simp only [d16973, d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39622 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d129471 q = 1) : d15349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d129471 q = 1) : d15350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d129471 q = 1) : d15351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d129471 q = 1) : d15352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d129471 q = 1) : d15353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39622 q ha hb
    | true =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d129471 q = 1) : d15354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d129471 q = 1) : d15355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d129471 q = 1) : d15356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d129471 q = 1) : d15357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d129471 q = 1) : d15358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39630 (p : Pattern) (ha : d16989 p = 1) (hb : d129471 p = 1) : d15364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d129471 q = 1) : d15353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39622 q ha hb
    | true =>
      simp only [d16978, d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d129471 q = 1) : d15354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d129471 q = 1) : d15355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d129471 q = 1) : d15356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d129471 q = 1) : d15357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d129471 q = 1) : d15359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39625 q ha hb
    | true =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d129471 q = 1) : d15360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d129471 q = 1) : d15361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d129471 q = 1) : d15362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d129471 q = 1) : d15363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d129471 q = 1) : d15364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39631 (p : Pattern) (ha : d16998 p = 1) (hb : d129471 p = 1) : d15373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d129471 q = 1) : d15359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39625 q ha hb
    | true =>
      simp only [d16984, d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d129471 q = 1) : d15360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d129471 q = 1) : d15361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d129471 q = 1) : d15362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d129471 q = 1) : d15363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d129471 q = 1) : d15373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39632 (p : Pattern) (ha : d17032 p = 1) (hb : d129471 p = 1) : d15408 p = 1 := by
  have h0 (q : Pattern) (ha : d1865 q = 1) (hb : d100904 q = 1) : d1865 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17031 q = 1) (hb : d129471 q = 1) : d15407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d129471, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17031, d129471, d15407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15401 q = 1) (hb : d129471 q = 1) : d15401 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17032 q = 1) (hb : d129471 q = 1) : d15408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17032, d15408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39633 (p : Pattern) (ha : d17058 p = 1) (hb : d129471 p = 1) : d15441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15435 q = 1) (hb : d129471 q = 1) : d15435 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17053 q = 1) (hb : d129471 q = 1) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17054 q = 1) (hb : d129471 q = 1) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17055 q = 1) (hb : d129471 q = 1) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17056 q = 1) (hb : d129471 q = 1) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17057 q = 1) (hb : d129471 q = 1) : d15440 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17057, d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17058 q = 1) (hb : d129471 q = 1) : d15441 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17058, d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39634 (p : Pattern) (ha : d17130 p = 1) (hb : d129471 p = 1) : d15521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d129471 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39633 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d129471 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d129471 q = 1) : d15518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d129471 q = 1) : d15519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d129471 q = 1) : d15520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d129471 q = 1) : d15521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39635 (p : Pattern) (ha : d17136 p = 1) (hb : d129471 p = 1) : d15527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d129471 q = 1) : d15522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39634 q ha hb
    | true =>
      simp only [d17131, d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d129471 q = 1) : d15523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d129471 q = 1) : d15524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d129471 q = 1) : d15525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d129471 q = 1) : d15526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d129471 q = 1) : d15527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39636 (p : Pattern) (ha : d16843 p = 1) (hb : d129471 p = 1) : d15212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d129471 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d129471 q = 1) : d15211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d129471 q = 1) : d15212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39637 (p : Pattern) (ha : d16845 p = 1) (hb : d129471 p = 1) : d15214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d129471 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d129471 q = 1) : d15213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d129471 q = 1) : d15214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39638 (p : Pattern) (ha : d16852 p = 1) (hb : d129471 p = 1) : d15221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d129471 q = 1) : d15219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d129471 q = 1) : d15220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d129471 q = 1) : d15221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39639 (p : Pattern) (ha : d16855 p = 1) (hb : d129471 p = 1) : d15224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d129471 q = 1) : d15222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d129471 q = 1) : d15223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d129471 q = 1) : d15224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39640 (p : Pattern) (ha : d16863 p = 1) (hb : d129471 p = 1) : d15232 p = 1 := by
  have h0 (q : Pattern) (ha : d1668 q = 1) (hb : d100904 q = 1) : d1668 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16861 q = 1) (hb : d129471 q = 1) : d15228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d129471, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16861, d129471, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15230 q = 1) (hb : d100904 q = 1) : d15230 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15152 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16862 q = 1) (hb : d129471 q = 1) : d15231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d129471, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16862, d129471, d15231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d16863 q = 1) (hb : d129471 q = 1) : d15232 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16863, d15232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39641 (p : Pattern) (ha : d16868 p = 1) (hb : d129471 p = 1) : d15237 p = 1 := by
  have h0 (q : Pattern) (ha : d13349 q = 1) (hb : d100904 q = 1) : d13349 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15157 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16867 q = 1) (hb : d129471 q = 1) : d15236 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d129471, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16867, d129471, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15158 q = 1) (hb : d129471 q = 1) : d15158 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16868 q = 1) (hb : d129471 q = 1) : d15237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16868, d15237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39642 (p : Pattern) (ha : d16874 p = 1) (hb : d129471 p = 1) : d15243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d129471 q = 1) : d15233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39640 q ha hb
    | true =>
      simp only [d16864, d15233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d129471 q = 1) : d15234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d15234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d129471 q = 1) : d15235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d15235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d129471 q = 1) : d15238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
    | true =>
      simp only [d16869, d15238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39641 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d129471 q = 1) : d15239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d15239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d129471 q = 1) : d15240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d15240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d129471 q = 1) : d15241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d129471 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d129471 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d129471 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15166 q = 1) (hb : d129471 q = 1) : d15166 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16799 q = 1) (hb : d129471 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16800 q = 1) (hb : d129471 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16801 q = 1) (hb : d129471 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16802 q = 1) (hb : d129471 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16873 q = 1) (hb : d129471 q = 1) : d15242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16874 q = 1) (hb : d129471 q = 1) : d15243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16874, d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39643 (p : Pattern) (ha : d16885 p = 1) (hb : d129471 p = 1) : d15254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d129471 q = 1) : d15244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39642 q ha hb
    | true =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d129471 q = 1) : d15245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d129471 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39627 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d129471 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d129471 q = 1) : d15251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d129471 q = 1) : d15252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d129471 q = 1) : d15253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d129471 q = 1) : d15254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39644 (p : Pattern) (ha : d16934 p = 1) (hb : d129471 p = 1) : d15309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d129471 q = 1) : d15160 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39617 q ha hb
    | true =>
      simp only [d16796, d15160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d129471 q = 1) : d15161 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d15161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d129471 q = 1) : d15162 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d15162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15166 q = 1) (hb : d129471 q = 1) : d15166 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16799 q = 1) (hb : d129471 q = 1) : d15167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16799, d15167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16800 q = 1) (hb : d129471 q = 1) : d15168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d15168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16801 q = 1) (hb : d129471 q = 1) : d15169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d15169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16802 q = 1) (hb : d129471 q = 1) : d15170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13287 q = 1) (hb : d129471 q = 1) : d13287 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16929 q = 1) (hb : d129471 q = 1) : d15304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39618 q ha hb
    | true =>
      simp only [d16929, d15304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16930 q = 1) (hb : d129471 q = 1) : d15305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d15305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16931 q = 1) (hb : d129471 q = 1) : d15306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d15306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16932 q = 1) (hb : d129471 q = 1) : d15307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16932, d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d16933 q = 1) (hb : d129471 q = 1) : d15308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16933, d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16934 q = 1) (hb : d129471 q = 1) : d15309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16934, d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16934, d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39645 (p : Pattern) (ha : d16940 p = 1) (hb : d129471 p = 1) : d15315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d129471 q = 1) : d15310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39644 q ha hb
    | true =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d129471 q = 1) : d15311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d129471 q = 1) : d15312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d129471 q = 1) : d15313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d129471 q = 1) : d15314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16940 q = 1) (hb : d129471 q = 1) : d15315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16940, d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16940, d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39646 (p : Pattern) (ha : d128357 p = 1) (hb : d129471 p = 1) : d125617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d129471 q = 1) : d15215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39636 q ha hb
    | true =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39637 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d129471 q = 1) : d15216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d129471 q = 1) : d15217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d129471 q = 1) : d15218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d129471 q = 1) : d15225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39638 q ha hb
    | true =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39639 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d129471 q = 1) : d15226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d129471 q = 1) : d15227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d129471 q = 1) : d15259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39643 q ha hb
    | true =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39628 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d129471 q = 1) : d125613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d129471 q = 1) : d15316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39645 q ha hb
    | true =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d129471 q = 1) : d15317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d129471 q = 1) : d125614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d129471 q = 1) : d125615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d129471 q = 1) : d125616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128357 q = 1) (hb : d129471 q = 1) : d125617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128357, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128357, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39647 (p : Pattern) (ha : d16947 p = 1) (hb : d129471 p = 1) : d15322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d129471 q = 1) : d15185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d129471 q = 1) : d15211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16947 q = 1) (hb : d129471 q = 1) : d15322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16947, d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16947, d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39648 (p : Pattern) (ha : d16948 p = 1) (hb : d129471 p = 1) : d15323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d129471 q = 1) : d15189 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d129471 q = 1) : d15213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16948 q = 1) (hb : d129471 q = 1) : d15323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16948, d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16948, d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39649 (p : Pattern) (ha : d16953 p = 1) (hb : d129471 p = 1) : d15328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d129471 q = 1) : d15178 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39619 q ha hb
    | true =>
      simp only [d16809, d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d129471 q = 1) : d15179 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d129471 q = 1) : d15184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d129471 q = 1) : d15219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d129471 q = 1) : d15220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16953 q = 1) (hb : d129471 q = 1) : d15328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16953, d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16953, d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39650 (p : Pattern) (ha : d16954 p = 1) (hb : d129471 p = 1) : d15329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d129471 q = 1) : d15188 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d129471 q = 1) : d15222 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d129471 q = 1) : d15223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16954 q = 1) (hb : d129471 q = 1) : d15329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16954, d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16954, d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39651 (p : Pattern) (ha : d16958 p = 1) (hb : d129471 p = 1) : d15333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d129471 q = 1) : d15244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39642 q ha hb
    | true =>
      simp only [d16875, d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d129471 q = 1) : d15245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d129471 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39627 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d129471 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d129471 q = 1) : d15251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d129471 q = 1) : d15252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d129471 q = 1) : d15253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16958 q = 1) (hb : d129471 q = 1) : d15333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16958, d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16958, d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39652 (p : Pattern) (ha : d16959 p = 1) (hb : d129471 p = 1) : d15334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d129471 q = 1) : d15249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39627 q ha hb
    | true =>
      simp only [d16880, d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d129471 q = 1) : d15250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d129471 q = 1) : d15182 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39620 q ha hb
    | true =>
      simp only [d16813, d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d129471 q = 1) : d15183 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d129471 q = 1) : d15255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d129471 q = 1) : d15256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d129471 q = 1) : d15257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16959 q = 1) (hb : d129471 q = 1) : d15334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16959, d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16959, d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39653 (p : Pattern) (ha : d16965 p = 1) (hb : d129471 p = 1) : d15340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16935 q = 1) (hb : d129471 q = 1) : d15310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39644 q ha hb
    | true =>
      simp only [d16935, d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16936 q = 1) (hb : d129471 q = 1) : d15311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16936, d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16937 q = 1) (hb : d129471 q = 1) : d15312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16937, d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16938 q = 1) (hb : d129471 q = 1) : d15313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16938, d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16939 q = 1) (hb : d129471 q = 1) : d15314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16939, d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16965 q = 1) (hb : d129471 q = 1) : d15340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16965, d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16965, d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39654 (p : Pattern) (ha : d128362 p = 1) (hb : d129471 p = 1) : d125622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16846 q = 1) (hb : d129471 q = 1) : d15215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39636 q ha hb
    | true =>
      simp only [d16846, d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39637 q ha hb
  have h2 (q : Pattern) (ha : d16847 q = 1) (hb : d129471 q = 1) : d15216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16847, d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16848 q = 1) (hb : d129471 q = 1) : d15217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16848, d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16849 q = 1) (hb : d129471 q = 1) : d15218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16849, d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16856 q = 1) (hb : d129471 q = 1) : d15225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39638 q ha hb
    | true =>
      simp only [d16856, d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39639 q ha hb
  have h6 (q : Pattern) (ha : d16857 q = 1) (hb : d129471 q = 1) : d15226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16857, d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16858 q = 1) (hb : d129471 q = 1) : d15227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16858, d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16890 q = 1) (hb : d129471 q = 1) : d15259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39643 q ha hb
    | true =>
      simp only [d16890, d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39628 q ha hb
  have h9 (q : Pattern) (ha : d128353 q = 1) (hb : d129471 q = 1) : d125613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128353, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16941 q = 1) (hb : d129471 q = 1) : d15316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39645 q ha hb
    | true =>
      simp only [d16941, d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16942 q = 1) (hb : d129471 q = 1) : d15317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16942, d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128354 q = 1) (hb : d129471 q = 1) : d125614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128354, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128355 q = 1) (hb : d129471 q = 1) : d125615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128355, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128356 q = 1) (hb : d129471 q = 1) : d125616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128356, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16949 q = 1) (hb : d129471 q = 1) : d15324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16949, d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39647 q ha hb
    | true =>
      simp only [d16949, d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39648 q ha hb
  have h16 (q : Pattern) (ha : d16950 q = 1) (hb : d129471 q = 1) : d15325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16950, d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16950, d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16951 q = 1) (hb : d129471 q = 1) : d15326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16951, d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16951, d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16952 q = 1) (hb : d129471 q = 1) : d15327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16952, d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16952, d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16955 q = 1) (hb : d129471 q = 1) : d15330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16955, d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39649 q ha hb
    | true =>
      simp only [d16955, d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39650 q ha hb
  have h20 (q : Pattern) (ha : d16956 q = 1) (hb : d129471 q = 1) : d15331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16956, d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16956, d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16957 q = 1) (hb : d129471 q = 1) : d15332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16957, d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16957, d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16960 q = 1) (hb : d129471 q = 1) : d15335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39651 q ha hb
    | true =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39652 q ha hb
  have h23 (q : Pattern) (ha : d128358 q = 1) (hb : d129471 q = 1) : d125618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16966 q = 1) (hb : d129471 q = 1) : d15341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39653 q ha hb
    | true =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16967 q = 1) (hb : d129471 q = 1) : d15342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128359 q = 1) (hb : d129471 q = 1) : d125619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128360 q = 1) (hb : d129471 q = 1) : d125620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128360, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128360, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128361 q = 1) (hb : d129471 q = 1) : d125621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128361, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128361, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128362 q = 1) (hb : d129471 q = 1) : d125622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128362, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128362, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro39655 (p : Pattern) (ha : d128369 p = 1) (hb : d129471 p = 1) : d125629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16960 q = 1) (hb : d129471 q = 1) : d15335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39651 q ha hb
    | true =>
      simp only [d16960, d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39652 q ha hb
  have h2 (q : Pattern) (ha : d128358 q = 1) (hb : d129471 q = 1) : d125618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128358, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16966 q = 1) (hb : d129471 q = 1) : d15341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39653 q ha hb
    | true =>
      simp only [d16966, d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16967 q = 1) (hb : d129471 q = 1) : d15342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16967, d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128359 q = 1) (hb : d129471 q = 1) : d125619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128359, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128367 q = 1) (hb : d129471 q = 1) : d125627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128367, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128367, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128368 q = 1) (hb : d129471 q = 1) : d125628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128368, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128368, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d129471 q = 1) : d125629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39656 (p : Pattern) (ha : d17010 p = 1) (hb : d129471 p = 1) : d15385 p = 1 := by
  have h0 (q : Pattern) (ha : d1856 q = 1) (hb : d100904 q = 1) : d1856 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17008 q = 1) (hb : d129471 q = 1) : d15379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d129471, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17008, d129471, d15379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15383 q = 1) (hb : d100904 q = 1) : d15383 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15390 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17009 q = 1) (hb : d129471 q = 1) : d15384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d129471, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17009, d129471, d15384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17010 q = 1) (hb : d129471 q = 1) : d15385 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17010, d15385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39657 (p : Pattern) (ha : d17017 p = 1) (hb : d129471 p = 1) : d15392 p = 1 := by
  have h0 (q : Pattern) (ha : d1860 q = 1) (hb : d100904 q = 1) : d1860 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17015 q = 1) (hb : d129471 q = 1) : d15386 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d129471, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17015, d129471, d15386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15390 q = 1) (hb : d100904 q = 1) : d15390 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17016 q = 1) (hb : d129471 q = 1) : d15391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d129471, d15391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17016, d129471, d15391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17017 q = 1) (hb : d129471 q = 1) : d15392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17017, d15392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39658 (p : Pattern) (ha : d17022 p = 1) (hb : d129471 p = 1) : d15402 p = 1 := by
  have h0 (q : Pattern) (ha : d13489 q = 1) (hb : d100904 q = 1) : d13489 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17021 q = 1) (hb : d129471 q = 1) : d15396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d129471, d15396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17021, d129471, d15396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15401 q = 1) (hb : d129471 q = 1) : d15401 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17022 q = 1) (hb : d129471 q = 1) : d15402 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17022, d15402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39659 (p : Pattern) (ha : d17041 p = 1) (hb : d129471 p = 1) : d15423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d129471 q = 1) : d15393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39656 q ha hb
    | true =>
      simp only [d17018, d15393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d129471 q = 1) : d15394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d15394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d129471 q = 1) : d15395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d15395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d129471 q = 1) : d15403 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
    | true =>
      simp only [d17023, d15403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39658 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d129471 q = 1) : d15404 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d15404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d129471 q = 1) : d15405 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d15405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d129471 q = 1) : d15406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d129471 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d129471 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d129471 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15417 q = 1) (hb : d129471 q = 1) : d15417 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17036 q = 1) (hb : d129471 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17037 q = 1) (hb : d129471 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17038 q = 1) (hb : d129471 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17039 q = 1) (hb : d129471 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17040 q = 1) (hb : d129471 q = 1) : d15422 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17041 q = 1) (hb : d129471 q = 1) : d15423 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17041, d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17041, d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39660 (p : Pattern) (ha : d17046 p = 1) (hb : d129471 p = 1) : d15428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d129471 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d129471 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d129471 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d129471 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d129471 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129471 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129471 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129471 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17044 q = 1) (hb : d129471 q = 1) : d15426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17044, d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17045 q = 1) (hb : d129471 q = 1) : d15427 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17045, d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17046 q = 1) (hb : d129471 q = 1) : d15428 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17046, d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17046, d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39661 (p : Pattern) (ha : d17052 p = 1) (hb : d129471 p = 1) : d15434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17042 q = 1) (hb : d129471 q = 1) : d15424 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17042, d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39659 q ha hb
    | true =>
      simp only [d17042, d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17043 q = 1) (hb : d129471 q = 1) : d15425 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17043, d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17043, d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17047 q = 1) (hb : d129471 q = 1) : d15429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39660 q ha hb
    | true =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17048 q = 1) (hb : d129471 q = 1) : d15430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17049 q = 1) (hb : d129471 q = 1) : d15431 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17049, d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17049, d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17050 q = 1) (hb : d129471 q = 1) : d15432 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17050, d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17050, d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17051 q = 1) (hb : d129471 q = 1) : d15433 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17051, d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17051, d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17052 q = 1) (hb : d129471 q = 1) : d15434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17052, d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17052, d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39662 (p : Pattern) (ha : d17064 p = 1) (hb : d129471 p = 1) : d15447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17047 q = 1) (hb : d129471 q = 1) : d15429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39660 q ha hb
    | true =>
      simp only [d17047, d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17048 q = 1) (hb : d129471 q = 1) : d15430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17048, d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d129471 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39633 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d129471 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17061 q = 1) (hb : d129471 q = 1) : d15444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17061, d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17061, d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17062 q = 1) (hb : d129471 q = 1) : d15445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17062, d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17062, d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17063 q = 1) (hb : d129471 q = 1) : d15446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17063, d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17063, d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17064 q = 1) (hb : d129471 q = 1) : d15447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17064, d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17064, d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39663 (p : Pattern) (ha : d17113 p = 1) (hb : d129471 p = 1) : d15504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d129471 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d129471 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d129471 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d129471 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d129471 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129471 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129471 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129471 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d129471 q = 1) : d13516 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17108 q = 1) (hb : d129471 q = 1) : d15499 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17108, d15499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17109 q = 1) (hb : d129471 q = 1) : d15500 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d15500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17110 q = 1) (hb : d129471 q = 1) : d15501 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d15501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17111 q = 1) (hb : d129471 q = 1) : d15502 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17111, d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17112 q = 1) (hb : d129471 q = 1) : d15503 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17112, d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17113 q = 1) (hb : d129471 q = 1) : d15504 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17113, d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17113, d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39664 (p : Pattern) (ha : d17119 p = 1) (hb : d129471 p = 1) : d15510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17114 q = 1) (hb : d129471 q = 1) : d15505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17114, d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39663 q ha hb
    | true =>
      simp only [d17114, d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17115 q = 1) (hb : d129471 q = 1) : d15506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17115, d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17115, d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17116 q = 1) (hb : d129471 q = 1) : d15507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17116, d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17116, d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17117 q = 1) (hb : d129471 q = 1) : d15508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17117, d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17117, d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17118 q = 1) (hb : d129471 q = 1) : d15509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17118, d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17118, d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17119 q = 1) (hb : d129471 q = 1) : d15510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17119, d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17119, d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39665 (p : Pattern) (ha : d128379 p = 1) (hb : d129471 p = 1) : d125639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17065 q = 1) (hb : d129471 q = 1) : d15448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17065, d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39661 q ha hb
    | true =>
      simp only [d17065, d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39662 q ha hb
  have h2 (q : Pattern) (ha : d128375 q = 1) (hb : d129471 q = 1) : d125635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128375, d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17120 q = 1) (hb : d129471 q = 1) : d15511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17120, d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39664 q ha hb
    | true =>
      simp only [d17120, d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17121 q = 1) (hb : d129471 q = 1) : d15512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17121, d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17121, d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d129471 q = 1) : d125636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128376, d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d129471 q = 1) : d125637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d129471 q = 1) : d125638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d129471 q = 1) : d125639 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39666 (p : Pattern) (ha : d128385 p = 1) (hb : d129471 p = 1) : d125645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16829 q = 1) (hb : d129471 q = 1) : d15198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16829, d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16829, d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39623 q ha hb
  have h2 (q : Pattern) (ha : d16830 q = 1) (hb : d129471 q = 1) : d15199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16830, d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16830, d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16839 q = 1) (hb : d129471 q = 1) : d15208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39623 q ha hb
    | true =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39626 q ha hb
  have h4 (q : Pattern) (ha : d16840 q = 1) (hb : d129471 q = 1) : d15209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16841 q = 1) (hb : d129471 q = 1) : d15210 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16841, d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16841, d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128363 q = 1) (hb : d129471 q = 1) : d125623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128363, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39646 q ha hb
    | true =>
      simp only [d128363, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39654 q ha hb
  have h7 (q : Pattern) (ha : d16990 q = 1) (hb : d129471 q = 1) : d15365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16990, d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39629 q ha hb
    | true =>
      simp only [d16990, d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39630 q ha hb
  have h8 (q : Pattern) (ha : d128364 q = 1) (hb : d129471 q = 1) : d125624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128364, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128364, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128365 q = 1) (hb : d129471 q = 1) : d125625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128365, d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128366 q = 1) (hb : d129471 q = 1) : d125626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128366, d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128370 q = 1) (hb : d129471 q = 1) : d125630 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128370, d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39655 q ha hb
  have h12 (q : Pattern) (ha : d16999 q = 1) (hb : d129471 q = 1) : d15374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16999, d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16999, d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39631 q ha hb
  have h13 (q : Pattern) (ha : d128371 q = 1) (hb : d129471 q = 1) : d125631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128371, d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128372 q = 1) (hb : d129471 q = 1) : d125632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128372, d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128373 q = 1) (hb : d129471 q = 1) : d125633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128373, d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128374 q = 1) (hb : d129471 q = 1) : d125634 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128374, d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128380 q = 1) (hb : d129471 q = 1) : d125640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128380, d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39665 q ha hb
  have h18 (q : Pattern) (ha : d17137 q = 1) (hb : d129471 q = 1) : d15528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17137, d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17137, d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39635 q ha hb
  have h19 (q : Pattern) (ha : d128381 q = 1) (hb : d129471 q = 1) : d125641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128381, d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128382 q = 1) (hb : d129471 q = 1) : d125642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128382, d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128383 q = 1) (hb : d129471 q = 1) : d125643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128383, d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128384 q = 1) (hb : d129471 q = 1) : d125644 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128384, d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128385 q = 1) (hb : d129471 q = 1) : d125645 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128385, d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39667 (p : Pattern) (ha : d128391 p = 1) (hb : d129471 p = 1) : d125651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d129471 q = 1) : d125646 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39666 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d129471 q = 1) : d125647 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d129471 q = 1) : d125648 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d129471 q = 1) : d125649 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d129471 q = 1) : d125650 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d129471 q = 1) : d125651 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39668 (p : Pattern) (ha : d17157 p = 1) (hb : d129471 p = 1) : d15546 p = 1 := by
  have h0 (q : Pattern) (ha : d2038 q = 1) (hb : d100904 q = 1) : d2038 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17155 q = 1) (hb : d129471 q = 1) : d15544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d129471, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17155, d129471, d15544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13676 q = 1) (hb : d100904 q = 1) : d13676 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15549 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17156 q = 1) (hb : d129471 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d129471, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17156, d129471, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17157 q = 1) (hb : d129471 q = 1) : d15546 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17157, d15546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39669 (p : Pattern) (ha : d17161 p = 1) (hb : d129471 p = 1) : d15551 p = 1 := by
  have h0 (q : Pattern) (ha : d2056 q = 1) (hb : d100904 q = 1) : d2056 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17160 q = 1) (hb : d129471 q = 1) : d15547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, d129471, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17160, d129471, d15547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15550 q = 1) (hb : d129471 q = 1) : d15550 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17161 q = 1) (hb : d129471 q = 1) : d15551 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17161, d15551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39670 (p : Pattern) (ha : d17174 p = 1) (hb : d129471 p = 1) : d15569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d129471 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d129471 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d129471 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d129471 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d129471 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d129471 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d129471 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d129471 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15563 q = 1) (hb : d129471 q = 1) : d15563 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17169 q = 1) (hb : d129471 q = 1) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17170 q = 1) (hb : d129471 q = 1) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17171 q = 1) (hb : d129471 q = 1) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17172 q = 1) (hb : d129471 q = 1) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17173 q = 1) (hb : d129471 q = 1) : d15568 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17173, d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17173, d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17174 q = 1) (hb : d129471 q = 1) : d15569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17174, d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17174, d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39671 (p : Pattern) (ha : d17178 p = 1) (hb : d129471 p = 1) : d15573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15563 q = 1) (hb : d129471 q = 1) : d15563 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17169 q = 1) (hb : d129471 q = 1) : d15564 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17169, d15564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17170 q = 1) (hb : d129471 q = 1) : d15565 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d15565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17171 q = 1) (hb : d129471 q = 1) : d15566 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d15566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17172 q = 1) (hb : d129471 q = 1) : d15567 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17172, d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17177 q = 1) (hb : d129471 q = 1) : d15572 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17177, d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17178 q = 1) (hb : d129471 q = 1) : d15573 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17178, d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17178, d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39672 (p : Pattern) (ha : d17184 p = 1) (hb : d129471 p = 1) : d15579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d129471 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d129471 q = 1) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17184 q = 1) (hb : d129471 q = 1) : d15579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17184, d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17184, d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39673 (p : Pattern) (ha : d17188 p = 1) (hb : d129471 p = 1) : d15583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d129471 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d129471 q = 1) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17188 q = 1) (hb : d129471 q = 1) : d15583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17188, d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17188, d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39674 (p : Pattern) (ha : d17194 p = 1) (hb : d129471 p = 1) : d15589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d129471 q = 1) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39672 q ha hb
    | true =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39673 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d129471 q = 1) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d129471 q = 1) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d129471 q = 1) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d129471 q = 1) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17194 q = 1) (hb : d129471 q = 1) : d15589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17194, d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17194, d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39675 (p : Pattern) (ha : d17197 p = 1) (hb : d129471 p = 1) : d15592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d129471 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17183 q = 1) (hb : d129471 q = 1) : d15578 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17183, d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17197 q = 1) (hb : d129471 q = 1) : d15592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17197, d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17197, d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39676 (p : Pattern) (ha : d17198 p = 1) (hb : d129471 p = 1) : d15593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d129471 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17187 q = 1) (hb : d129471 q = 1) : d15582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17187, d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17198 q = 1) (hb : d129471 q = 1) : d15593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17198, d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17198, d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39677 (p : Pattern) (ha : d17204 p = 1) (hb : d129471 p = 1) : d15599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17189 q = 1) (hb : d129471 q = 1) : d15584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39672 q ha hb
    | true =>
      simp only [d17189, d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39673 q ha hb
  have h2 (q : Pattern) (ha : d17190 q = 1) (hb : d129471 q = 1) : d15585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17190, d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17191 q = 1) (hb : d129471 q = 1) : d15586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17191, d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17192 q = 1) (hb : d129471 q = 1) : d15587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17192, d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17193 q = 1) (hb : d129471 q = 1) : d15588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17193, d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17199 q = 1) (hb : d129471 q = 1) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39675 q ha hb
    | true =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39676 q ha hb
  have h7 (q : Pattern) (ha : d17200 q = 1) (hb : d129471 q = 1) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17201 q = 1) (hb : d129471 q = 1) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17202 q = 1) (hb : d129471 q = 1) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17203 q = 1) (hb : d129471 q = 1) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17204 q = 1) (hb : d129471 q = 1) : d15599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17204, d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17204, d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39678 (p : Pattern) (ha : d17244 p = 1) (hb : d129471 p = 1) : d15636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d129471 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d129471 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d129471 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d129471 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d129471 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d129471 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d129471 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d129471 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17242 q = 1) (hb : d129471 q = 1) : d15634 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17242, d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17243 q = 1) (hb : d129471 q = 1) : d15635 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17243, d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17244 q = 1) (hb : d129471 q = 1) : d15636 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17244, d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17244, d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39679 (p : Pattern) (ha : d17254 p = 1) (hb : d129471 p = 1) : d15646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d129471 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39678 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d129471 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d129471 q = 1) : d15643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d129471 q = 1) : d15644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d129471 q = 1) : d15645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17254 q = 1) (hb : d129471 q = 1) : d15646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17254, d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17254, d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39680 (p : Pattern) (ha : d17348 p = 1) (hb : d129471 p = 1) : d15746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17338 q = 1) (hb : d129471 q = 1) : d15736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17338, d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39679 q ha hb
    | true =>
      simp only [d17338, d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39673 q ha hb
  have h2 (q : Pattern) (ha : d17339 q = 1) (hb : d129471 q = 1) : d15737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17339, d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17339, d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17340 q = 1) (hb : d129471 q = 1) : d15738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17340, d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17340, d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17341 q = 1) (hb : d129471 q = 1) : d15739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17341, d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17341, d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17342 q = 1) (hb : d129471 q = 1) : d15740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17342, d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17342, d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17343 q = 1) (hb : d129471 q = 1) : d15741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39673 q ha hb
    | true =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17344 q = 1) (hb : d129471 q = 1) : d15742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17345 q = 1) (hb : d129471 q = 1) : d15743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17346 q = 1) (hb : d129471 q = 1) : d15744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17347 q = 1) (hb : d129471 q = 1) : d15745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17348 q = 1) (hb : d129471 q = 1) : d15746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17348, d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17348, d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39681 (p : Pattern) (ha : d17354 p = 1) (hb : d129471 p = 1) : d15752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17343 q = 1) (hb : d129471 q = 1) : d15741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39673 q ha hb
    | true =>
      simp only [d17343, d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17344 q = 1) (hb : d129471 q = 1) : d15742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17344, d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17345 q = 1) (hb : d129471 q = 1) : d15743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17345, d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17346 q = 1) (hb : d129471 q = 1) : d15744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17346, d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17347 q = 1) (hb : d129471 q = 1) : d15745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17347, d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17349 q = 1) (hb : d129471 q = 1) : d15747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39676 q ha hb
    | true =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17350 q = 1) (hb : d129471 q = 1) : d15748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17351 q = 1) (hb : d129471 q = 1) : d15749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17352 q = 1) (hb : d129471 q = 1) : d15750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17353 q = 1) (hb : d129471 q = 1) : d15751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17354 q = 1) (hb : d129471 q = 1) : d15752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17354, d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17354, d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39682 (p : Pattern) (ha : d17363 p = 1) (hb : d129471 p = 1) : d15761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17349 q = 1) (hb : d129471 q = 1) : d15747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39676 q ha hb
    | true =>
      simp only [d17349, d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17350 q = 1) (hb : d129471 q = 1) : d15748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17350, d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17351 q = 1) (hb : d129471 q = 1) : d15749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17351, d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17352 q = 1) (hb : d129471 q = 1) : d15750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17352, d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17353 q = 1) (hb : d129471 q = 1) : d15751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17353, d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17363 q = 1) (hb : d129471 q = 1) : d15761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17363, d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17363, d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39683 (p : Pattern) (ha : d17396 p = 1) (hb : d129471 p = 1) : d15786 p = 1 := by
  have h0 (q : Pattern) (ha : d2343 q = 1) (hb : d100904 q = 1) : d2343 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17395 q = 1) (hb : d129471 q = 1) : d15785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d129471, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17395, d129471, d15785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15779 q = 1) (hb : d129471 q = 1) : d15779 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17396 q = 1) (hb : d129471 q = 1) : d15786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17396, d15786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39684 (p : Pattern) (ha : d17422 p = 1) (hb : d129471 p = 1) : d15819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15813 q = 1) (hb : d129471 q = 1) : d15813 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17417 q = 1) (hb : d129471 q = 1) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17418 q = 1) (hb : d129471 q = 1) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17419 q = 1) (hb : d129471 q = 1) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17420 q = 1) (hb : d129471 q = 1) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17421 q = 1) (hb : d129471 q = 1) : d15818 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17421, d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17422 q = 1) (hb : d129471 q = 1) : d15819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17422, d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17422, d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro39685 (p : Pattern) (ha : d17494 p = 1) (hb : d129471 p = 1) : d15899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17423 q = 1) (hb : d129471 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39684 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17424 q = 1) (hb : d129471 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17491 q = 1) (hb : d129471 q = 1) : d15896 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17491, d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17491, d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17492 q = 1) (hb : d129471 q = 1) : d15897 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17492, d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17492, d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17493 q = 1) (hb : d129471 q = 1) : d15898 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17493, d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17493, d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17494 q = 1) (hb : d129471 q = 1) : d15899 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17494, d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17494, d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39686 (p : Pattern) (ha : d17500 p = 1) (hb : d129471 p = 1) : d15905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17495 q = 1) (hb : d129471 q = 1) : d15900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17495, d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39685 q ha hb
    | true =>
      simp only [d17495, d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17496 q = 1) (hb : d129471 q = 1) : d15901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17496, d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17496, d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17497 q = 1) (hb : d129471 q = 1) : d15902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17497, d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17497, d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17498 q = 1) (hb : d129471 q = 1) : d15903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17498, d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17498, d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17499 q = 1) (hb : d129471 q = 1) : d15904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17499, d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17499, d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17500 q = 1) (hb : d129471 q = 1) : d15905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17500, d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17500, d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39687 (p : Pattern) (ha : d17209 p = 1) (hb : d129471 p = 1) : d15604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d129471 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d129471 q = 1) : d15603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17209 q = 1) (hb : d129471 q = 1) : d15604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17209, d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17209, d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39688 (p : Pattern) (ha : d17211 p = 1) (hb : d129471 p = 1) : d15606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d129471 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d129471 q = 1) : d15605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17211 q = 1) (hb : d129471 q = 1) : d15606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17211, d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17211, d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39689 (p : Pattern) (ha : d17218 p = 1) (hb : d129471 p = 1) : d15613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d129471 q = 1) : d15611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d129471 q = 1) : d15612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17218 q = 1) (hb : d129471 q = 1) : d15613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17218, d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17218, d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39690 (p : Pattern) (ha : d17221 p = 1) (hb : d129471 p = 1) : d15616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d129471 q = 1) : d15614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d129471 q = 1) : d15615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17221 q = 1) (hb : d129471 q = 1) : d15616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17221, d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17221, d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39691 (p : Pattern) (ha : d17229 p = 1) (hb : d129471 p = 1) : d15621 p = 1 := by
  have h0 (q : Pattern) (ha : d2147 q = 1) (hb : d100904 q = 1) : d2147 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17227 q = 1) (hb : d129471 q = 1) : d15620 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d129471, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17227, d129471, d15620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17228 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, d129471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17228, d129471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17229 q = 1) (hb : d129471 q = 1) : d15621 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17229, d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39692 (p : Pattern) (ha : d17233 p = 1) (hb : d129471 p = 1) : d15625 p = 1 := by
  have h0 (q : Pattern) (ha : d13676 q = 1) (hb : d100904 q = 1) : d13676 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17156 q = 1) (hb : d129471 q = 1) : d15545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, d129471, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17156, d129471, d15545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15550 q = 1) (hb : d129471 q = 1) : d15550 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17233 q = 1) (hb : d129471 q = 1) : d15625 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17233, d15625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39693 (p : Pattern) (ha : d17239 p = 1) (hb : d129471 p = 1) : d15631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d129471 q = 1) : d15622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39691 q ha hb
    | true =>
      simp only [d17230, d15622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d129471 q = 1) : d15623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d129471 q = 1) : d15624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d129471 q = 1) : d15626 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
    | true =>
      simp only [d17234, d15626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39692 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d129471 q = 1) : d15627 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d15627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d129471 q = 1) : d15628 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d15628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d129471 q = 1) : d15629 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d129471 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d129471 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d129471 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15558 q = 1) (hb : d129471 q = 1) : d15558 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17165 q = 1) (hb : d129471 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17166 q = 1) (hb : d129471 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17167 q = 1) (hb : d129471 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17168 q = 1) (hb : d129471 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17238 q = 1) (hb : d129471 q = 1) : d15630 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17239 q = 1) (hb : d129471 q = 1) : d15631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17239, d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17239, d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39694 (p : Pattern) (ha : d17250 p = 1) (hb : d129471 p = 1) : d15642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d129471 q = 1) : d15632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39693 q ha hb
    | true =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d129471 q = 1) : d15633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d129471 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39678 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d129471 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d129471 q = 1) : d15639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d129471 q = 1) : d15640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d129471 q = 1) : d15641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17250 q = 1) (hb : d129471 q = 1) : d15642 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17250, d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17250, d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39695 (p : Pattern) (ha : d17299 p = 1) (hb : d129471 p = 1) : d15697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d129471 q = 1) : d15552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39668 q ha hb
    | true =>
      simp only [d17162, d15552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d129471 q = 1) : d15553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d15553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d129471 q = 1) : d15554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d15554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15558 q = 1) (hb : d129471 q = 1) : d15558 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17165 q = 1) (hb : d129471 q = 1) : d15559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17165, d15559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17166 q = 1) (hb : d129471 q = 1) : d15560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d15560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17167 q = 1) (hb : d129471 q = 1) : d15561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d15561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17168 q = 1) (hb : d129471 q = 1) : d15562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13614 q = 1) (hb : d129471 q = 1) : d13614 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17294 q = 1) (hb : d129471 q = 1) : d15692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39669 q ha hb
    | true =>
      simp only [d17294, d15692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17295 q = 1) (hb : d129471 q = 1) : d15693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d15693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17296 q = 1) (hb : d129471 q = 1) : d15694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d15694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17297 q = 1) (hb : d129471 q = 1) : d15695 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17297, d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17298 q = 1) (hb : d129471 q = 1) : d15696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17298, d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17299 q = 1) (hb : d129471 q = 1) : d15697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17299, d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17299, d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39696 (p : Pattern) (ha : d17305 p = 1) (hb : d129471 p = 1) : d15703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d129471 q = 1) : d15698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39695 q ha hb
    | true =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d129471 q = 1) : d15699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d129471 q = 1) : d15700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d129471 q = 1) : d15701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d129471 q = 1) : d15702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17305 q = 1) (hb : d129471 q = 1) : d15703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17305, d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17305, d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39697 (p : Pattern) (ha : d128400 p = 1) (hb : d129471 p = 1) : d125660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d129471 q = 1) : d15607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39687 q ha hb
    | true =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39688 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d129471 q = 1) : d15608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d129471 q = 1) : d15609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d129471 q = 1) : d15610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d129471 q = 1) : d15617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39689 q ha hb
    | true =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39690 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d129471 q = 1) : d15618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d129471 q = 1) : d15619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d129471 q = 1) : d15647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39694 q ha hb
    | true =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39679 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d129471 q = 1) : d125656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d129471 q = 1) : d15704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39696 q ha hb
    | true =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d129471 q = 1) : d15705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d129471 q = 1) : d125657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d129471 q = 1) : d125658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d129471 q = 1) : d125659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128400 q = 1) (hb : d129471 q = 1) : d125660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128400, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128400, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39698 (p : Pattern) (ha : d17312 p = 1) (hb : d129471 p = 1) : d15710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17182 q = 1) (hb : d129471 q = 1) : d15577 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17182, d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17208 q = 1) (hb : d129471 q = 1) : d15603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17208, d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17312 q = 1) (hb : d129471 q = 1) : d15710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17312, d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17312, d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39699 (p : Pattern) (ha : d17313 p = 1) (hb : d129471 p = 1) : d15711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17186 q = 1) (hb : d129471 q = 1) : d15581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17186, d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17210 q = 1) (hb : d129471 q = 1) : d15605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17210, d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17313 q = 1) (hb : d129471 q = 1) : d15711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17313, d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17313, d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39700 (p : Pattern) (ha : d17318 p = 1) (hb : d129471 p = 1) : d15716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17175 q = 1) (hb : d129471 q = 1) : d15570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39670 q ha hb
    | true =>
      simp only [d17175, d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17176 q = 1) (hb : d129471 q = 1) : d15571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17176, d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17181 q = 1) (hb : d129471 q = 1) : d15576 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17181, d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17216 q = 1) (hb : d129471 q = 1) : d15611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17216, d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17217 q = 1) (hb : d129471 q = 1) : d15612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17217, d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17318 q = 1) (hb : d129471 q = 1) : d15716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17318, d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17318, d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39701 (p : Pattern) (ha : d17319 p = 1) (hb : d129471 p = 1) : d15717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17185 q = 1) (hb : d129471 q = 1) : d15580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17185, d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17219 q = 1) (hb : d129471 q = 1) : d15614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17219, d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17220 q = 1) (hb : d129471 q = 1) : d15615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17220, d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17319 q = 1) (hb : d129471 q = 1) : d15717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17319, d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17319, d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39702 (p : Pattern) (ha : d17323 p = 1) (hb : d129471 p = 1) : d15721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17240 q = 1) (hb : d129471 q = 1) : d15632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39693 q ha hb
    | true =>
      simp only [d17240, d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17241 q = 1) (hb : d129471 q = 1) : d15633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17241, d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17245 q = 1) (hb : d129471 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39678 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17246 q = 1) (hb : d129471 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17247 q = 1) (hb : d129471 q = 1) : d15639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17247, d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17248 q = 1) (hb : d129471 q = 1) : d15640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17248, d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17249 q = 1) (hb : d129471 q = 1) : d15641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17249, d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17323 q = 1) (hb : d129471 q = 1) : d15721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17323, d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17323, d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39703 (p : Pattern) (ha : d17324 p = 1) (hb : d129471 p = 1) : d15722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17245 q = 1) (hb : d129471 q = 1) : d15637 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39678 q ha hb
    | true =>
      simp only [d17245, d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17246 q = 1) (hb : d129471 q = 1) : d15638 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17246, d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17179 q = 1) (hb : d129471 q = 1) : d15574 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39671 q ha hb
    | true =>
      simp only [d17179, d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17180 q = 1) (hb : d129471 q = 1) : d15575 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17180, d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17251 q = 1) (hb : d129471 q = 1) : d15643 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17251, d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17252 q = 1) (hb : d129471 q = 1) : d15644 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17252, d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17253 q = 1) (hb : d129471 q = 1) : d15645 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17253, d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17324 q = 1) (hb : d129471 q = 1) : d15722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17324, d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17324, d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39704 (p : Pattern) (ha : d17330 p = 1) (hb : d129471 p = 1) : d15728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17300 q = 1) (hb : d129471 q = 1) : d15698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39695 q ha hb
    | true =>
      simp only [d17300, d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17301 q = 1) (hb : d129471 q = 1) : d15699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17301, d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17302 q = 1) (hb : d129471 q = 1) : d15700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17302, d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17303 q = 1) (hb : d129471 q = 1) : d15701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17303, d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17304 q = 1) (hb : d129471 q = 1) : d15702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17304, d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17330 q = 1) (hb : d129471 q = 1) : d15728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17330, d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17330, d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39705 (p : Pattern) (ha : d128405 p = 1) (hb : d129471 p = 1) : d125665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17212 q = 1) (hb : d129471 q = 1) : d15607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39687 q ha hb
    | true =>
      simp only [d17212, d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39688 q ha hb
  have h2 (q : Pattern) (ha : d17213 q = 1) (hb : d129471 q = 1) : d15608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17213, d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17214 q = 1) (hb : d129471 q = 1) : d15609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17214, d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17215 q = 1) (hb : d129471 q = 1) : d15610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17215, d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17222 q = 1) (hb : d129471 q = 1) : d15617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39689 q ha hb
    | true =>
      simp only [d17222, d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39690 q ha hb
  have h6 (q : Pattern) (ha : d17223 q = 1) (hb : d129471 q = 1) : d15618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17223, d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17224 q = 1) (hb : d129471 q = 1) : d15619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17224, d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17255 q = 1) (hb : d129471 q = 1) : d15647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39694 q ha hb
    | true =>
      simp only [d17255, d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39679 q ha hb
  have h9 (q : Pattern) (ha : d128396 q = 1) (hb : d129471 q = 1) : d125656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128396, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17306 q = 1) (hb : d129471 q = 1) : d15704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39696 q ha hb
    | true =>
      simp only [d17306, d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17307 q = 1) (hb : d129471 q = 1) : d15705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17307, d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128397 q = 1) (hb : d129471 q = 1) : d125657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128397, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128398 q = 1) (hb : d129471 q = 1) : d125658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128398, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128399 q = 1) (hb : d129471 q = 1) : d125659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128399, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17314 q = 1) (hb : d129471 q = 1) : d15712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17314, d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39698 q ha hb
    | true =>
      simp only [d17314, d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39699 q ha hb
  have h16 (q : Pattern) (ha : d17315 q = 1) (hb : d129471 q = 1) : d15713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17315, d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17315, d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17316 q = 1) (hb : d129471 q = 1) : d15714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17316, d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17316, d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d17317 q = 1) (hb : d129471 q = 1) : d15715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17317, d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17317, d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17320 q = 1) (hb : d129471 q = 1) : d15718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17320, d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39700 q ha hb
    | true =>
      simp only [d17320, d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39701 q ha hb
  have h20 (q : Pattern) (ha : d17321 q = 1) (hb : d129471 q = 1) : d15719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17321, d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17321, d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17322 q = 1) (hb : d129471 q = 1) : d15720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17322, d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17322, d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d17325 q = 1) (hb : d129471 q = 1) : d15723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39702 q ha hb
    | true =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39703 q ha hb
  have h23 (q : Pattern) (ha : d128401 q = 1) (hb : d129471 q = 1) : d125661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d17331 q = 1) (hb : d129471 q = 1) : d15729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39704 q ha hb
    | true =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d17332 q = 1) (hb : d129471 q = 1) : d15730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128402 q = 1) (hb : d129471 q = 1) : d125662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128403 q = 1) (hb : d129471 q = 1) : d125663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128403, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128403, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128404 q = 1) (hb : d129471 q = 1) : d125664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128404, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128404, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128405 q = 1) (hb : d129471 q = 1) : d125665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128405, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128405, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro39706 (p : Pattern) (ha : d128412 p = 1) (hb : d129471 p = 1) : d125672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17325 q = 1) (hb : d129471 q = 1) : d15723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39702 q ha hb
    | true =>
      simp only [d17325, d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39703 q ha hb
  have h2 (q : Pattern) (ha : d128401 q = 1) (hb : d129471 q = 1) : d125661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128401, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17331 q = 1) (hb : d129471 q = 1) : d15729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39704 q ha hb
    | true =>
      simp only [d17331, d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17332 q = 1) (hb : d129471 q = 1) : d15730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17332, d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128402 q = 1) (hb : d129471 q = 1) : d125662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128402, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128410 q = 1) (hb : d129471 q = 1) : d125670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128410, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128410, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128411 q = 1) (hb : d129471 q = 1) : d125671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128411, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128411, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d129471 q = 1) : d125672 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39707 (p : Pattern) (ha : d17375 p = 1) (hb : d129471 p = 1) : d15768 p = 1 := by
  have h0 (q : Pattern) (ha : d2334 q = 1) (hb : d100904 q = 1) : d2334 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17373 q = 1) (hb : d129471 q = 1) : d15767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d129471, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17373, d129471, d15767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17374 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d129471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17374, d129471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17375 q = 1) (hb : d129471 q = 1) : d15768 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17375, d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39708 (p : Pattern) (ha : d17382 p = 1) (hb : d129471 p = 1) : d15771 p = 1 := by
  have h0 (q : Pattern) (ha : d2338 q = 1) (hb : d100904 q = 1) : d2338 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17379 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17380 q = 1) (hb : d129471 q = 1) : d15769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d129471, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17380, d129471, d15769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13816 q = 1) (hb : d100904 q = 1) : d13816 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15778 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17381 q = 1) (hb : d129471 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d129471, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17381, d129471, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d17382 q = 1) (hb : d129471 q = 1) : d15771 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17382, d15771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39709 (p : Pattern) (ha : d17386 p = 1) (hb : d129471 p = 1) : d15780 p = 1 := by
  have h0 (q : Pattern) (ha : d13816 q = 1) (hb : d100904 q = 1) : d13816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17381 q = 1) (hb : d129471 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d129471, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17381, d129471, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15779 q = 1) (hb : d129471 q = 1) : d15779 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17386 q = 1) (hb : d129471 q = 1) : d15780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro39710 (p : Pattern) (ha : d17405 p = 1) (hb : d129471 p = 1) : d15801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d129471 q = 1) : d15772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39707 q ha hb
    | true =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d129471 q = 1) : d15773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d129471 q = 1) : d15774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d129471 q = 1) : d15781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
    | true =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39709 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d129471 q = 1) : d15782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d129471 q = 1) : d15783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d129471 q = 1) : d15784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d129471 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d129471 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d129471 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15795 q = 1) (hb : d129471 q = 1) : d15795 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17400 q = 1) (hb : d129471 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17401 q = 1) (hb : d129471 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17402 q = 1) (hb : d129471 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17403 q = 1) (hb : d129471 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17404 q = 1) (hb : d129471 q = 1) : d15800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17405 q = 1) (hb : d129471 q = 1) : d15801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro39711 (p : Pattern) (ha : d17410 p = 1) (hb : d129471 p = 1) : d15806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d129471 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d129471 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d129471 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d129471 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d129471 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129471 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129471 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129471 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17408 q = 1) (hb : d129471 q = 1) : d15804 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17409 q = 1) (hb : d129471 q = 1) : d15805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17410 q = 1) (hb : d129471 q = 1) : d15806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro39712 (p : Pattern) (ha : d17416 p = 1) (hb : d129471 p = 1) : d15812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d129471 q = 1) : d15802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39710 q ha hb
    | true =>
      simp only [d17406, d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d129471 q = 1) : d15803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d129471 q = 1) : d15807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39711 q ha hb
    | true =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d129471 q = 1) : d15808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d129471 q = 1) : d15809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d129471 q = 1) : d15810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d129471 q = 1) : d15811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d129471 q = 1) : d15812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39713 (p : Pattern) (ha : d17428 p = 1) (hb : d129471 p = 1) : d15825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d129471 q = 1) : d15807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39711 q ha hb
    | true =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d129471 q = 1) : d15808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d129471 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39684 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d129471 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d129471 q = 1) : d15822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d129471 q = 1) : d15823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d129471 q = 1) : d15824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d129471 q = 1) : d15825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39714 (p : Pattern) (ha : d17477 p = 1) (hb : d129471 p = 1) : d15882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d129471 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d129471 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d129471 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d129471 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d129471 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129471 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129471 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129471 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d129471 q = 1) : d13843 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17472 q = 1) (hb : d129471 q = 1) : d15877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17472, d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17473 q = 1) (hb : d129471 q = 1) : d15878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17474 q = 1) (hb : d129471 q = 1) : d15879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17475 q = 1) (hb : d129471 q = 1) : d15880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17475, d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17476 q = 1) (hb : d129471 q = 1) : d15881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17476, d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17477 q = 1) (hb : d129471 q = 1) : d15882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17477, d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro39715 (p : Pattern) (ha : d17483 p = 1) (hb : d129471 p = 1) : d15888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d129471 q = 1) : d15883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39714 q ha hb
    | true =>
      simp only [d17478, d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d129471 q = 1) : d15884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d129471 q = 1) : d15885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d129471 q = 1) : d15886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d129471 q = 1) : d15887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d129471 q = 1) : d15888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39716 (p : Pattern) (ha : d128422 p = 1) (hb : d129471 p = 1) : d125682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d129471 q = 1) : d15826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39712 q ha hb
    | true =>
      simp only [d17429, d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39713 q ha hb
  have h2 (q : Pattern) (ha : d128418 q = 1) (hb : d129471 q = 1) : d125678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128418, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d129471 q = 1) : d15889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39715 q ha hb
    | true =>
      simp only [d17484, d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d129471 q = 1) : d15890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d129471 q = 1) : d125679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d129471 q = 1) : d125680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d129471 q = 1) : d125681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d129471 q = 1) : d125682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39717 (p : Pattern) (ha : d128428 p = 1) (hb : d129471 p = 1) : d125688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17195 q = 1) (hb : d129471 q = 1) : d15590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17195, d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17195, d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39674 q ha hb
  have h2 (q : Pattern) (ha : d17196 q = 1) (hb : d129471 q = 1) : d15591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17196, d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17196, d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17205 q = 1) (hb : d129471 q = 1) : d15600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39674 q ha hb
    | true =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39677 q ha hb
  have h4 (q : Pattern) (ha : d17206 q = 1) (hb : d129471 q = 1) : d15601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17207 q = 1) (hb : d129471 q = 1) : d15602 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17207, d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17207, d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128406 q = 1) (hb : d129471 q = 1) : d125666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39697 q ha hb
    | true =>
      simp only [d128406, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39705 q ha hb
  have h7 (q : Pattern) (ha : d17355 q = 1) (hb : d129471 q = 1) : d15753 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17355, d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39680 q ha hb
    | true =>
      simp only [d17355, d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39681 q ha hb
  have h8 (q : Pattern) (ha : d128407 q = 1) (hb : d129471 q = 1) : d125667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128407, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128408 q = 1) (hb : d129471 q = 1) : d125668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128408, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128409 q = 1) (hb : d129471 q = 1) : d125669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128409, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128413 q = 1) (hb : d129471 q = 1) : d125673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128413, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39706 q ha hb
  have h12 (q : Pattern) (ha : d17364 q = 1) (hb : d129471 q = 1) : d15762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17364, d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39682 q ha hb
  have h13 (q : Pattern) (ha : d128414 q = 1) (hb : d129471 q = 1) : d125674 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128414, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128415 q = 1) (hb : d129471 q = 1) : d125675 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128415, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128416 q = 1) (hb : d129471 q = 1) : d125676 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128416, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128417 q = 1) (hb : d129471 q = 1) : d125677 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128417, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128423 q = 1) (hb : d129471 q = 1) : d125683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128423, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39716 q ha hb
  have h18 (q : Pattern) (ha : d17501 q = 1) (hb : d129471 q = 1) : d15906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17501, d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39686 q ha hb
  have h19 (q : Pattern) (ha : d128424 q = 1) (hb : d129471 q = 1) : d125684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128424, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128425 q = 1) (hb : d129471 q = 1) : d125685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128425, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128426 q = 1) (hb : d129471 q = 1) : d125686 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128426, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128427 q = 1) (hb : d129471 q = 1) : d125687 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128427, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128428 q = 1) (hb : d129471 q = 1) : d125688 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128428, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro39718 (p : Pattern) (ha : d128434 p = 1) (hb : d129471 p = 1) : d125694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d129471 q = 1) : d125689 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39717 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d129471 q = 1) : d125690 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d129471 q = 1) : d125691 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d129471 q = 1) : d125692 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d129471 q = 1) : d125693 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d129471 q = 1) : d125694 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39719 (p : Pattern) (ha : d128440 p = 1) (hb : d129471 p = 1) : d125700 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d129471 q = 1) : d125529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39477 q ha hb
    | true =>
      simp only [d128269, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39519 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d129471 q = 1) : d125569 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39565 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d129471 q = 1) : d125570 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d129471 q = 1) : d125610 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39616 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d129471 q = 1) : d125611 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d129471 q = 1) : d125612 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d129471 q = 1) : d125652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39667 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d129471 q = 1) : d125653 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d129471 q = 1) : d125654 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d129471 q = 1) : d125655 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d129471 q = 1) : d125695 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39718 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d129471 q = 1) : d125696 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d129471 q = 1) : d125697 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d129471 q = 1) : d125698 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d129471 q = 1) : d125699 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d129471 q = 1) : d125700 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro39720 (p : Pattern) (ha : d128446 p = 1) (hb : d129471 p = 1) : d125706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d129471 q = 1) : d125701 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39719 q ha hb
    | true =>
      simp only [d128441, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d129471 q = 1) : d125702 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d129471 q = 1) : d125703 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d129471 q = 1) : d125704 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d129471 q = 1) : d125705 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d129471 q = 1) : d125706 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39721 (p : Pattern) (ha : d128452 p = 1) (hb : d129471 p = 1) : d125712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d129471 q = 1) : d125707 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39720 q ha hb
    | true =>
      simp only [d128447, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d129471 q = 1) : d125708 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d129471 q = 1) : d125709 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d129471 q = 1) : d125710 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d129471 q = 1) : d125711 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d129471 q = 1) : d125712 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39722 (p : Pattern) (ha : d128458 p = 1) (hb : d129471 p = 1) : d125718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d129471 q = 1) : d125713 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39721 q ha hb
    | true =>
      simp only [d128453, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d129471 q = 1) : d125714 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d129471 q = 1) : d125715 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d129471 q = 1) : d125716 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d129471 q = 1) : d125717 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d129471 q = 1) : d125718 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39723 (p : Pattern) (ha : d128464 p = 1) (hb : d129471 p = 1) : d125724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d129471 q = 1) : d125719 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39722 q ha hb
    | true =>
      simp only [d128459, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d129471 q = 1) : d125720 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d129471 q = 1) : d125721 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d129471 q = 1) : d125722 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d129471 q = 1) : d125723 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d129471 q = 1) : d125724 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39724 (p : Pattern) (ha : d128470 p = 1) (hb : d129471 p = 1) : d125730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d129471 q = 1) : d125725 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39723 q ha hb
    | true =>
      simp only [d128465, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d129471 q = 1) : d125726 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d129471 q = 1) : d125727 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d129471 q = 1) : d125728 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d129471 q = 1) : d125729 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d129471 q = 1) : d125730 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39725 (p : Pattern) (ha : d128476 p = 1) (hb : d129471 p = 1) : d125736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d129471 q = 1) : d125731 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39724 q ha hb
    | true =>
      simp only [d128471, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d129471 q = 1) : d125732 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d129471 q = 1) : d125733 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d129471 q = 1) : d125734 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d129471 q = 1) : d125735 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d129471 q = 1) : d125736 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39726 (p : Pattern) (ha : d128482 p = 1) (hb : d129471 p = 1) : d125742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d129471 q = 1) : d125737 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39725 q ha hb
    | true =>
      simp only [d128477, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d129471 q = 1) : d125738 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d129471 q = 1) : d125739 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d129471 q = 1) : d125740 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d129471 q = 1) : d125741 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d129471 q = 1) : d125742 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro39727 (p : Pattern) (ha : d13981 p = 1) (hb : d122308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13980 q = 1) (hb : d122307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13981 q = 1) (hb : d122308 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13981, d122308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13981, d122308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39728 (p : Pattern) (ha : d13987 p = 1) (hb : d122314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13982 q = 1) (hb : d122309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39727 q ha hb
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d13983 q = 1) (hb : d122310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13984 q = 1) (hb : d122311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d13985 q = 1) (hb : d122312 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13986 q = 1) (hb : d122313 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, d122313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13986, d122313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13987 q = 1) (hb : d122314 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, d122314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13987, d122314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39729 (p : Pattern) (ha : d13993 p = 1) (hb : d122320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d122317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d122318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d122319 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13993 q = 1) (hb : d122320 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, d122320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, d122320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39730 (p : Pattern) (ha : d122326 p = 1) (hb : d125417 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d122322, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122326 q = 1) (hb : d125417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122326, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122326, d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39731 (p : Pattern) (ha : d14000 p = 1) (hb : d122327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d122317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d122318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d122319 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14000 q = 1) (hb : d122327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, d122327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14000, d122327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39732 (p : Pattern) (ha : d122333 p = 1) (hb : d125422 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122322 q = 1) (hb : d125413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122322, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d122322, d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d122323 q = 1) (hb : d125414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122323, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122323, d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122324 q = 1) (hb : d125415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122324, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122324, d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122325 q = 1) (hb : d125416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122325, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122325, d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d14001 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39731 q ha hb
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d122329 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d122329, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d122330 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d122330, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d122331 q = 1) (hb : d125420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122331, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d122331, d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d122332 q = 1) (hb : d125421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122332, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d122332, d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d122333 q = 1) (hb : d125422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122333, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122333, d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro39733 (p : Pattern) (ha : d122340 p = 1) (hb : d125429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39731 q ha hb
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122329 q = 1) (hb : d125418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122329, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122329, d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122330 q = 1) (hb : d125419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122330, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122330, d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122338 q = 1) (hb : d125427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122338, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122338, d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122339 q = 1) (hb : d125428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122339, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122339, d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122340 q = 1) (hb : d125429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122340, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122340, d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39734 (p : Pattern) (ha : d14020 p = 1) (hb : d122347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14019 q = 1) (hb : d122346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h9 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d14020 q = 1) (hb : d122347 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14020, d122347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14020, d122347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro39735 (p : Pattern) (ha : d14026 p = 1) (hb : d122353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14021 q = 1) (hb : d122348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39734 q ha hb
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d14022 q = 1) (hb : d122349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14023 q = 1) (hb : d122350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d14024 q = 1) (hb : d122351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14025 q = 1) (hb : d122352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, d122352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14025, d122352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14026 q = 1) (hb : d122353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, d122353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14026, d122353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro39736 (p : Pattern) (ha : d14032 p = 1) (hb : d122359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d122354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39735 q ha hb
    | true =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d122355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d14029 q = 1) (hb : d122356 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, d122356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, d122356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14030 q = 1) (hb : d122357 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, d122357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14030, d122357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14031 q = 1) (hb : d122358 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, d122358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14031, d122358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14032 q = 1) (hb : d122359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, d122359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14032, d122359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro39737 (p : Pattern) (ha : d122365 p = 1) (hb : d125439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d122360 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39736 q ha hb
    | true =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122361 q = 1) (hb : d125435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122361, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122361, d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d122362 q = 1) (hb : d125436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122362, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122362, d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d122363 q = 1) (hb : d125437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122363, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122363, d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122364 q = 1) (hb : d125438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122364, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122364, d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122365 q = 1) (hb : d125439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122365, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122365, d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro39738 (p : Pattern) (ha : d122371 p = 1) (hb : d125445 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d122334 q = 1) (hb : d125423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122334, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39730 q ha hb
    | true =>
      simp only [d122334, d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39732 q ha hb
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
  have h8 (q : Pattern) (ha : d122335 q = 1) (hb : d125424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122335, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122335, d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122336 q = 1) (hb : d125425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122336, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d122336, d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122337 q = 1) (hb : d125426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122337, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d122337, d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122341 q = 1) (hb : d125430 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122341, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122341, d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39733 q ha hb
  have h12 (q : Pattern) (ha : d122342 q = 1) (hb : d125431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122342, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d122342, d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122343 q = 1) (hb : d125432 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122343, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122343, d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122344 q = 1) (hb : d125433 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122344, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122344, d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122345 q = 1) (hb : d125434 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122345, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122345, d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122366 q = 1) (hb : d125440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122366, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122366, d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39737 q ha hb
  have h17 (q : Pattern) (ha : d122367 q = 1) (hb : d125441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122367, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122367, d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d122368 q = 1) (hb : d125442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122368, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122368, d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d122369 q = 1) (hb : d125443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122369, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d122369, d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d122370 q = 1) (hb : d125444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122370, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d122370, d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122371 q = 1) (hb : d125445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122371, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122371, d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro39739 (p : Pattern) (ha : d14054 p = 1) (hb : d122381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d122377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d122378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d122379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d122380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14054 q = 1) (hb : d122381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d122381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d122381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39740 (p : Pattern) (ha : d14061 p = 1) (hb : d122388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d122377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d122378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d122379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d122380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14001 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39731 q ha hb
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d14057 q = 1) (hb : d122384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d122384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d122384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14058 q = 1) (hb : d122385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d122385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14058, d122385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14059 q = 1) (hb : d122386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d122386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d122386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14060 q = 1) (hb : d122387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d122387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d122387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14061 q = 1) (hb : d122388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d122388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14061, d122388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39741 (p : Pattern) (ha : d14141 p = 1) (hb : d122451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d122377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d122378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d122379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d122380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d14141 q = 1) (hb : d122451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, d122451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14141, d122451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39742 (p : Pattern) (ha : d14066 p = 1) (hb : d122393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d122317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d122318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d122392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14066 q = 1) (hb : d122393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, d122393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, d122393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39743 (p : Pattern) (ha : d14073 p = 1) (hb : d122400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d122317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d122398 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d122399 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14073 q = 1) (hb : d122400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, d122400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, d122400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39744 (p : Pattern) (ha : d14079 p = 1) (hb : d122406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14077 q = 1) (hb : d122404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14078 q = 1) (hb : d122405 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14079 q = 1) (hb : d122406 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14079, d122406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14079, d122406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro39745 (p : Pattern) (ha : d14085 p = 1) (hb : d122412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d122407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39744 q ha hb
    | true =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39727 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d122408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d122409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13982 q = 1) (hb : d122309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39727 q ha hb
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h5 (q : Pattern) (ha : d13983 q = 1) (hb : d122310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13984 q = 1) (hb : d122311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14083 q = 1) (hb : d122410 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13985 q = 1) (hb : d122312 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14084 q = 1) (hb : d122411 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, d122411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14084, d122411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14085 q = 1) (hb : d122412 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, d122412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14085, d122412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro39746 (p : Pattern) (ha : d14091 p = 1) (hb : d122418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d122413 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39745 q ha hb
    | true =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d122414 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d122415 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d122416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d122417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d122418 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, d122418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, d122418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro39747 (p : Pattern) (ha : d14112 p = 1) (hb : d122424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d122421 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d122422 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d122423 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d122424 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, d122424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, d122424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro39748 (p : Pattern) (ha : d122430 p = 1) (hb : d125455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d122394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39742 q ha hb
    | true =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d122395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d122396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d122401 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39743 q ha hb
    | true =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d122402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39746 q ha hb
    | true =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d122420 q = 1) (hb : d125451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122420, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d122420, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14113 q = 1) (hb : d122425 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39747 q ha hb
    | true =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14114 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d122427 q = 1) (hb : d125452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122427, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122427, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122428 q = 1) (hb : d125453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122428, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d122428, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122429 q = 1) (hb : d125454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122429, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122429, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122430 q = 1) (hb : d125455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122430, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122430, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro39749 (p : Pattern) (ha : d14119 p = 1) (hb : d122431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122315 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39728 q ha hb
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122316 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d122317 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d122318 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d122392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14119 q = 1) (hb : d122431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, d122431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14119, d122431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
