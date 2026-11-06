import NetHack.Soko22Hazard87.AndIntroBlocks0052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro13250 (p : Pattern) (ha : d7169 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2373 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7165 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7165, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d7166 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7167 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7168 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d7169 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13251 (p : Pattern) (ha : d7173 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6655 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d7170 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7171 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7172 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d7173 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13252 (p : Pattern) (ha : d73774 p = 1) (hb : d82259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7174 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13250 q ha hb
    | true =>
      simp only [d7174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13251 q ha hb
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13249 q ha hb
    | true =>
      simp only [d6672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d73774 q = 1) (hb : d82258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d73774 q = 1) (hb : d82259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13253 (p : Pattern) (ha : d73774 p = 1) (hb : d82265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13223 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13223 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13226 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13239 q ha hb
    | true =>
      simp only [d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13247 q ha hb
  have h7 (q : Pattern) (ha : d7149 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13232 q ha hb
    | true =>
      simp only [d7149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13227 q ha hb
  have h8 (q : Pattern) (ha : d73774 q = 1) (hb : d82244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d73774 q = 1) (hb : d82245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d82245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d73774 q = 1) (hb : d82246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d73774 q = 1) (hb : d82250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13248 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13228 q ha hb
  have h13 (q : Pattern) (ha : d73774 q = 1) (hb : d82251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d73774 q = 1) (hb : d82252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d82252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d73774 q = 1) (hb : d82253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d73774 q = 1) (hb : d82254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d73774 q = 1) (hb : d82260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13252 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13230 q ha hb
  have h19 (q : Pattern) (ha : d73774 q = 1) (hb : d82261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d73774 q = 1) (hb : d82262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d82262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d73774 q = 1) (hb : d82263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d73774 q = 1) (hb : d82264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d73774 q = 1) (hb : d82265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13254 (p : Pattern) (ha : d73774 p = 1) (hb : d82271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13253 q ha hb
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13255 (p : Pattern) (ha : d73774 p = 1) (hb : d82277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d73774 q = 1) (hb : d82106 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13084 q ha hb
    | true =>
      simp only [d82106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13118 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82146 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13152 q ha hb
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82147 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82187 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13186 q ha hb
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82188 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82189 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d73774 q = 1) (hb : d82229 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13220 q ha hb
  have h8 (q : Pattern) (ha : d73774 q = 1) (hb : d82230 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d73774 q = 1) (hb : d82231 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d73774 q = 1) (hb : d82232 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d73774 q = 1) (hb : d82272 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13254 q ha hb
  have h12 (q : Pattern) (ha : d73774 q = 1) (hb : d82273 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d73774 q = 1) (hb : d82274 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d73774 q = 1) (hb : d82275 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d73774 q = 1) (hb : d82276 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d73774 q = 1) (hb : d82277 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro13256 (p : Pattern) (ha : d73774 p = 1) (hb : d82283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82278 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13255 q ha hb
    | true =>
      simp only [d82278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82279 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82280 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82281 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82282 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82283 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13257 (p : Pattern) (ha : d73774 p = 1) (hb : d82289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82284 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13256 q ha hb
    | true =>
      simp only [d82284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82285 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82286 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82287 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82288 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82289 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13258 (p : Pattern) (ha : d73774 p = 1) (hb : d82295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82290 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13257 q ha hb
    | true =>
      simp only [d82290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82291 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82292 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82293 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82294 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82295 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13259 (p : Pattern) (ha : d73774 p = 1) (hb : d82301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82296 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13258 q ha hb
    | true =>
      simp only [d82296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82297 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d73774 q = 1) (hb : d82298 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d73774 q = 1) (hb : d82299 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d73774 q = 1) (hb : d82300 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d73774 q = 1) (hb : d82301 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13260 (p : Pattern) (ha : d82307 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d73774 q = 1) (hb : d82302 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13259 q ha hb
    | true =>
      simp only [d82302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d73774 q = 1) (hb : d82303 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82304 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d98788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82304, d98788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d82305 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82306 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d82307 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro13261 (p : Pattern) (ha : d82313 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13260 q ha hb
    | true =>
      simp only [d82308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13262 (p : Pattern) (ha : d82319 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13261 q ha hb
    | true =>
      simp only [d82314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13263 (p : Pattern) (ha : d53647 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13049 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13050 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13067 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13068 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13264 (p : Pattern) (ha : d53655 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13052 q ha hb
    | true =>
      simp only [d204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13043 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13265 (p : Pattern) (ha : d53665 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13054 q ha hb
    | true =>
      simp only [d244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13046 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13266 (p : Pattern) (ha : d53671 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13064 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13065 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13264 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13265 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13267 (p : Pattern) (ha : d53677 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13263 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13266 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13268 (p : Pattern) (ha : d53680 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13088 q ha hb
    | true =>
      simp only [d502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13089 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13269 (p : Pattern) (ha : d689 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d676 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d684 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d686 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d687 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d688 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d689 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13270 (p : Pattern) (ha : d53691 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13269 q ha hb
    | true =>
      simp only [d53686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13093 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13271 (p : Pattern) (ha : d53697 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13087 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13090 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13268 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13270 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13272 (p : Pattern) (ha : d53703 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13271 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13273 (p : Pattern) (ha : d53707 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13122 q ha hb
    | true =>
      simp only [d794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13123 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13274 (p : Pattern) (ha : d1011 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d998 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1006 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1009 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1010 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d1011 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13275 (p : Pattern) (ha : d53718 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13274 q ha hb
    | true =>
      simp only [d53713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13127 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13276 (p : Pattern) (ha : d53724 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13121 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13124 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13273 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13275 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13277 (p : Pattern) (ha : d53730 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13276 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13278 (p : Pattern) (ha : d53735 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13156 q ha hb
    | true =>
      simp only [d1173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13157 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13279 (p : Pattern) (ha : d1436 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1423 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1431 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1434 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1435 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d1436 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13280 (p : Pattern) (ha : d53746 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13279 q ha hb
    | true =>
      simp only [d53741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13161 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13281 (p : Pattern) (ha : d53752 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13155 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13158 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13278 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13280 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13282 (p : Pattern) (ha : d53758 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13281 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13283 (p : Pattern) (ha : d53764 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13190 q ha hb
    | true =>
      simp only [d1634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13191 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13284 (p : Pattern) (ha : d1913 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1911 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1912 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d1913 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13285 (p : Pattern) (ha : d53775 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13284 q ha hb
    | true =>
      simp only [d53770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13195 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13286 (p : Pattern) (ha : d53781 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13189 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13192 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13283 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13285 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13287 (p : Pattern) (ha : d53787 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13286 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13288 (p : Pattern) (ha : d53794 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13224 q ha hb
    | true =>
      simp only [d2117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13225 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13289 (p : Pattern) (ha : d2391 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2386 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2388 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2389 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2390 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d2391 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro13290 (p : Pattern) (ha : d53805 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13289 q ha hb
    | true =>
      simp only [d53800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13229 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13291 (p : Pattern) (ha : d53811 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13223 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13226 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13288 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13290 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13292 (p : Pattern) (ha : d53817 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13291 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13293 (p : Pattern) (ha : d53823 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13267 q ha hb
    | true =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13272 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13277 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13282 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13287 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13292 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro13294 (p : Pattern) (ha : d53829 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13293 q ha hb
    | true =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13295 (p : Pattern) (ha : d53835 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13294 q ha hb
    | true =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13296 (p : Pattern) (ha : d53841 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13295 q ha hb
    | true =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13297 (p : Pattern) (ha : d53847 p = 1) (hb : d73774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13296 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13298 (p : Pattern) (ha : d53853 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13297 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53850 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d98788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d98788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53851 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53852 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53853 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro13299 (p : Pattern) (ha : d53859 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13298 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
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
theorem andIntro13300 (p : Pattern) (ha : d53865 p = 1) (hb : d98788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13299 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d98788 q = 1) : d0 q = 1 := by
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
theorem andIntro13301 (p : Pattern) (ha : d82319 p = 1) (hb : d98791 p = 1) : d82319 p = 1 := by
  have h0 (q : Pattern) (ha : d82319 q = 1) (hb : d98791 q = 1) : d82319 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro13302 (p : Pattern) (ha : d1 p = 1) (hb : d82319 p = 1) : d82319 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d82319 q = 1) : d82319 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro13303 (p : Pattern) (ha : d53865 p = 1) (hb : d98791 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d98791 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro13304 (p : Pattern) (ha : d1 p = 1) (hb : d53865 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53865 q = 1) : d53865 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro13305 (p : Pattern) (ha : d0 p = 1) (hb : d53865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53865 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro13306 (p : Pattern) (ha : d4349 p = 1) (hb : d70145 p = 1) : d76799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d70145 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d70145 q = 1) : d5856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d70145 q = 1) : d76788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d70145 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d70145 q = 1) : d76789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d70145 q = 1) : d76797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d70145 q = 1) : d76798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d70145 q = 1) : d76799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13307 (p : Pattern) (ha : d4359 p = 1) (hb : d70145 p = 1) : d76809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d70145 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d70145 q = 1) : d5874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d5874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
    | true =>
      simp only [d244, d5874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d70145 q = 1) : d76805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d70145 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d70145 q = 1) : d76806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d70145 q = 1) : d76807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d70145 q = 1) : d76808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d70145 q = 1) : d76809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13308 (p : Pattern) (ha : d51643 p = 1) (hb : d70145 p = 1) : d76787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d70145 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d70145 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d70145 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d70145 q = 1) : d5850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d70145 q = 1) : d76783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d70145 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d70145 q = 1) : d76784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d70145 q = 1) : d76785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d70145 q = 1) : d76786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d70145 q = 1) : d76787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro13309 (p : Pattern) (ha : d51646 p = 1) (hb : d70145 p = 1) : d76792 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d70145 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d70145 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d70145 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d70145 q = 1) : d5850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d70145 q = 1) : d76783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d70145 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d70145 q = 1) : d76784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d70145 q = 1) : d76785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d70145 q = 1) : d76786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d70145 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d70145 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d70145 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d70145 q = 1) : d5856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d70145 q = 1) : d76788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d70145 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d70145 q = 1) : d76789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d70145 q = 1) : d76790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d70145 q = 1) : d76791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d70145 q = 1) : d76792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro13310 (p : Pattern) (ha : d51652 p = 1) (hb : d70145 p = 1) : d76815 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d70145 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d70145 q = 1) : d76793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13308 q ha hb
    | true =>
      simp only [d51647, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13309 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d70145 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d70145 q = 1) : d76794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d70145 q = 1) : d76795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d70145 q = 1) : d76796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d70145 q = 1) : d76800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13306 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d70145 q = 1) : d76801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d70145 q = 1) : d76802 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d70145 q = 1) : d76803 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d70145 q = 1) : d76804 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d70145 q = 1) : d76810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13307 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d70145 q = 1) : d76811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d70145 q = 1) : d76812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d70145 q = 1) : d76813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d70145 q = 1) : d76814 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d70145 q = 1) : d76815 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro13311 (p : Pattern) (ha : d284 p = 1) (hb : d70145 p = 1) : d5895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d70145 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d70145 q = 1) : d5850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d70145 q = 1) : d5891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d70145 q = 1) : d5892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d70145 q = 1) : d5893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d70145 q = 1) : d5894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d70145 q = 1) : d5895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d5895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d5895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13312 (p : Pattern) (ha : d291 p = 1) (hb : d70145 p = 1) : d5902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d70145 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d70145 q = 1) : d5850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d70145 q = 1) : d5891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d70145 q = 1) : d5892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d70145 q = 1) : d5893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d70145 q = 1) : d5894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d70145 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d70145 q = 1) : d5856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d70145 q = 1) : d5898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d5898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d5898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d70145 q = 1) : d5899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d70145 q = 1) : d5900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d70145 q = 1) : d5901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d70145 q = 1) : d5902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d5902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d5902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13313 (p : Pattern) (ha : d397 p = 1) (hb : d70145 p = 1) : d5952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d70145 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d70145 q = 1) : d5850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
    | true =>
      simp only [d157, d5850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d70145 q = 1) : d5891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d5891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d70145 q = 1) : d5892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d5892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d70145 q = 1) : d5893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d5893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d70145 q = 1) : d5894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d5894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d70145 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d70145 q = 1) : d5952 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d5952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d5952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13314 (p : Pattern) (ha : d6745 p = 1) (hb : d70145 p = 1) : d5921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d332 q = 1) : d332 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6742 q = 1) (hb : d70145 q = 1) : d5918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6742, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6742, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6743 q = 1) (hb : d70145 q = 1) : d5919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6743, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6743, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6744 q = 1) (hb : d70145 q = 1) : d5920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6744, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6744, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6745 q = 1) (hb : d70145 q = 1) : d5921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6745, d5921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6745, d5921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13315 (p : Pattern) (ha : d70145 p = 1) (hb : d82032 p = 1) : d76825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d70145 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d70145 q = 1) : d5908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d5908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7825 q ha hb
    | true =>
      simp only [d297, d5908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d70145 q = 1) : d5909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d5909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d5909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d70145 q = 1) : d5910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d70145 q = 1) : d5911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d70145 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d70145 q = 1) : d5915 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d5915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7826 q ha hb
    | true =>
      simp only [d304, d5915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d70145 q = 1) : d5916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d5916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d5916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d70145 q = 1) : d5917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6746 q = 1) (hb : d70145 q = 1) : d5922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6746, d5922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13314 q ha hb
    | true =>
      simp only [d6746, d5922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82028 q = 1) : d76821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82028, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82028, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d70145 q = 1) : d5350 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82029 q = 1) : d76822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82029, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82029, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82030 q = 1) : d76823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82030, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82030, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82031 q = 1) : d76824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82031, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82031, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82032 q = 1) : d76825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82032, d76825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82032, d76825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13316 (p : Pattern) (ha : d6752 p = 1) (hb : d70145 p = 1) : d5942 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d332 q = 1) : d332 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6742 q = 1) (hb : d70145 q = 1) : d5918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6742, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6742, d70145, d5918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6743 q = 1) (hb : d70145 q = 1) : d5919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6743, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6743, d5919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6744 q = 1) (hb : d70145 q = 1) : d5920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6744, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6744, d5920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6752 q = 1) (hb : d70145 q = 1) : d5942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6752, d5942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6752, d5942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13317 (p : Pattern) (ha : d70145 p = 1) (hb : d82037 p = 1) : d76830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d70145 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d70145 q = 1) : d5908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d5908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7825 q ha hb
    | true =>
      simp only [d297, d5908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d70145 q = 1) : d5909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d5909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d5909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d70145 q = 1) : d5910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d5910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d70145 q = 1) : d5911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d5911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d70145 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d70145 q = 1) : d5915 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d5915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7826 q ha hb
    | true =>
      simp only [d304, d5915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d70145 q = 1) : d5916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d5916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d5916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d70145 q = 1) : d5917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d5917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6746 q = 1) (hb : d70145 q = 1) : d5922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6746, d5922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13314 q ha hb
    | true =>
      simp only [d6746, d5922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4469 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82028 q = 1) : d76821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82028, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82028, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d70145 q = 1) : d5350 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82029 q = 1) : d76822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82029, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82029, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82030 q = 1) : d76823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82030, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82030, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82031 q = 1) : d76824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82031, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82031, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194 q = 1) (hb : d70145 q = 1) : d194 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d377 q = 1) (hb : d70145 q = 1) : d5934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d5934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7828 q ha hb
    | true =>
      simp only [d377, d5934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d378 q = 1) (hb : d70145 q = 1) : d5935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d5935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d5935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d379 q = 1) (hb : d70145 q = 1) : d5936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d5936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d379, d5936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d380 q = 1) (hb : d70145 q = 1) : d5937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d5937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d5937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d199 q = 1) (hb : d70145 q = 1) : d199 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d382 q = 1) (hb : d70145 q = 1) : d5939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d5939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7829 q ha hb
    | true =>
      simp only [d382, d5939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d383 q = 1) (hb : d70145 q = 1) : d5940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d5940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d5940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d384 q = 1) (hb : d70145 q = 1) : d5941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d5941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d384, d5941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6753 q = 1) (hb : d70145 q = 1) : d5943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6753, d5943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13316 q ha hb
    | true =>
      simp only [d6753, d5943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82033 q = 1) : d76826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82033, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82033, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d5357 q = 1) (hb : d70145 q = 1) : d5357 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82034 q = 1) : d76827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82034, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82034, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82035 q = 1) : d76828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82035, d76828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82035, d76828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82036 q = 1) : d76829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82036, d76829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82036, d76829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82037 q = 1) : d76830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82037, d76830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82037, d76830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13318 (p : Pattern) (ha : d70145 p = 1) (hb : d82044 p = 1) : d76837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6753 q = 1) (hb : d70145 q = 1) : d5943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6753, d5943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13316 q ha hb
    | true =>
      simp only [d6753, d5943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82033 q = 1) : d76826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82033, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82033, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5357 q = 1) (hb : d70145 q = 1) : d5357 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82034 q = 1) : d76827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82034, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82034, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82042 q = 1) : d76835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82042, d76835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82042, d76835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82043 q = 1) : d76836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82043, d76836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82043, d76836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82044 q = 1) : d76837 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82044, d76837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82044, d76837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13319 (p : Pattern) (ha : d6778 p = 1) (hb : d70145 p = 1) : d5968 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d425 q = 1) : d425 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6775 q = 1) (hb : d70145 q = 1) : d5965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6775, d70145, d5965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6775, d70145, d5965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6776 q = 1) (hb : d70145 q = 1) : d5966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6776, d5966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6776, d5966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6777 q = 1) (hb : d70145 q = 1) : d5967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6777, d5967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6777, d5967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6778 q = 1) (hb : d70145 q = 1) : d5968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6778, d5968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6778, d5968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13320 (p : Pattern) (ha : d70145 p = 1) (hb : d82054 p = 1) : d76847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6779 q = 1) (hb : d70145 q = 1) : d5969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6779, d5969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13319 q ha hb
    | true =>
      simp only [d6779, d5969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82050 q = 1) : d76843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82050, d76843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82050, d76843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5379 q = 1) (hb : d70145 q = 1) : d5379 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82051 q = 1) : d76844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82051, d76844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82051, d76844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82052 q = 1) : d76845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82052, d76845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82052, d76845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82053 q = 1) : d76846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82053, d76846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82053, d76846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82054 q = 1) : d76847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82054, d76847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82054, d76847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13321 (p : Pattern) (ha : d70145 p = 1) (hb : d82060 p = 1) : d76853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d70145 q = 1) : d5896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d5896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d5896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13311 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d70145 q = 1) : d5897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d5897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d5897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d70145 q = 1) : d5903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13311 q ha hb
    | true =>
      simp only [d292, d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13312 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d70145 q = 1) : d5904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d70145 q = 1) : d5905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d5905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d5905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82038 q = 1) : d76831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82038, d76831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13315 q ha hb
    | true =>
      simp only [d82038, d76831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13317 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d70145 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d70145 q = 1) : d5953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d5953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13313 q ha hb
    | true =>
      simp only [d398, d5953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82039 q = 1) : d76832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82039, d76832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82039, d76832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82040 q = 1) : d76833 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82040, d76833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82040, d76833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82041 q = 1) : d76834 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82041, d76834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82041, d76834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82045 q = 1) : d76838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82045, d76838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82045, d76838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13318 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d70145 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82046 q = 1) : d76839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82046, d76839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82046, d76839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82047 q = 1) : d76840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82047, d76840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82047, d76840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82048 q = 1) : d76841 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82048, d76841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82048, d76841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82049 q = 1) : d76842 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82049, d76842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82049, d76842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82055 q = 1) : d76848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82055, d76848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82055, d76848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13320 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d70145 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82056 q = 1) : d76849 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82056, d76849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82056, d76849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82057 q = 1) : d76850 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82057, d76850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82057, d76850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82058 q = 1) : d76851 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82058, d76851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82058, d76851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82059 q = 1) : d76852 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82059, d76852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82059, d76852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82060 q = 1) : d76853 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82060, d76853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82060, d76853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13322 (p : Pattern) (ha : d70145 p = 1) (hb : d82066 p = 1) : d76859 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d70145 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d70145 q = 1) : d76816 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13310 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d70145 q = 1) : d76817 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d70145 q = 1) : d76818 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d70145 q = 1) : d76819 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d70145 q = 1) : d76820 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82061 q = 1) : d76854 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82061, d76854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82061, d76854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13321 q ha hb
  have h8 (q : Pattern) (ha : d70145 q = 1) (hb : d82062 q = 1) : d76855 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82062, d76855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82062, d76855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82063 q = 1) : d76856 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82063, d76856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82063, d76856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82064 q = 1) : d76857 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82064, d76857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82064, d76857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82065 q = 1) : d76858 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82065, d76858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82065, d76858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82066 q = 1) : d76859 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82066, d76859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d82066, d76859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro13323 (p : Pattern) (ha : d497 p = 1) (hb : d70145 p = 1) : d5997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d70145 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d70145 q = 1) : d5992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d5992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4480 q ha hb
    | true =>
      simp only [d492, d5992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d70145 q = 1) : d5993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d5993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d5993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d70145 q = 1) : d5994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d70145 q = 1) : d5995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d70145 q = 1) : d5996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d497 q = 1) (hb : d70145 q = 1) : d5997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d5997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d5997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13324 (p : Pattern) (ha : d507 p = 1) (hb : d70145 p = 1) : d6005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d70145 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d492 q = 1) (hb : d70145 q = 1) : d5992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d5992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4480 q ha hb
    | true =>
      simp only [d492, d5992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d70145 q = 1) : d5993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d5993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d5993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d70145 q = 1) : d5994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d5994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d70145 q = 1) : d5995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d5995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d70145 q = 1) : d5996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d5996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d70145 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d502 q = 1) (hb : d70145 q = 1) : d6000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d6000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4476 q ha hb
    | true =>
      simp only [d502, d6000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d503 q = 1) (hb : d70145 q = 1) : d6001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d6001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d6001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d504 q = 1) (hb : d70145 q = 1) : d6002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d504, d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d505 q = 1) (hb : d70145 q = 1) : d6003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d506 q = 1) (hb : d70145 q = 1) : d6004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d507 q = 1) (hb : d70145 q = 1) : d6005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d6005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d507, d6005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13325 (p : Pattern) (ha : d6809 p = 1) (hb : d70145 p = 1) : d4830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4826 q = 1) : d4826 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6806 q = 1) (hb : d70145 q = 1) : d4827 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6806, d70145, d4827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6806, d70145, d4827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6807 q = 1) (hb : d70145 q = 1) : d4828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6807, d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6807, d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6808 q = 1) (hb : d70145 q = 1) : d4829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6808, d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6808, d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6809 q = 1) (hb : d70145 q = 1) : d4830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6809, d4830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6809, d4830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13326 (p : Pattern) (ha : d6830 p = 1) (hb : d70145 p = 1) : d6061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d70145 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6825 q = 1) (hb : d70145 q = 1) : d6056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6825, d6056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13325 q ha hb
    | true =>
      simp only [d6825, d6056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6826 q = 1) (hb : d70145 q = 1) : d6057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6826, d6057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6826, d6057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6827 q = 1) (hb : d70145 q = 1) : d6058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6827, d6058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6827, d6058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6828 q = 1) (hb : d70145 q = 1) : d6059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6828, d6059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6828, d6059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6829 q = 1) (hb : d70145 q = 1) : d6060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6829, d6060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6829, d6060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d70145 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6830 q = 1) (hb : d70145 q = 1) : d6061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6830, d6061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6830, d6061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13327 (p : Pattern) (ha : d6805 p = 1) (hb : d70145 p = 1) : d6024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d556 q = 1) : d556 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6802 q = 1) (hb : d70145 q = 1) : d6021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6802, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6802, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6803 q = 1) (hb : d70145 q = 1) : d6022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6803, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6803, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6804 q = 1) (hb : d70145 q = 1) : d6023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6804, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6804, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6805 q = 1) (hb : d70145 q = 1) : d6024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6805, d6024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6805, d6024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13328 (p : Pattern) (ha : d70145 p = 1) (hb : d82071 p = 1) : d76864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d70145 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d70145 q = 1) : d6011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d6011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7837 q ha hb
    | true =>
      simp only [d515, d6011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d70145 q = 1) : d6012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d6012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d6012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d70145 q = 1) : d6013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d70145 q = 1) : d6014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d70145 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d70145 q = 1) : d6018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d6018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7838 q ha hb
    | true =>
      simp only [d525, d6018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d70145 q = 1) : d6019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d6019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d6019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d70145 q = 1) : d6020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6810 q = 1) (hb : d70145 q = 1) : d6025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6810, d6025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13327 q ha hb
    | true =>
      simp only [d6810, d6025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13325 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82067 q = 1) : d76860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82067, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82067, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d70145 q = 1) : d5401 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82068 q = 1) : d76861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82068, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82068, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82069 q = 1) : d76862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82069, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82069, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82070 q = 1) : d76863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82070, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82070, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82071 q = 1) : d76864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82071, d76864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82071, d76864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13329 (p : Pattern) (ha : d6816 p = 1) (hb : d70145 p = 1) : d6045 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d556 q = 1) : d556 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6802 q = 1) (hb : d70145 q = 1) : d6021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6802, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6802, d70145, d6021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6803 q = 1) (hb : d70145 q = 1) : d6022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6803, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6803, d6022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6804 q = 1) (hb : d70145 q = 1) : d6023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6804, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6804, d6023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6816 q = 1) (hb : d70145 q = 1) : d6045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6816, d6045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6816, d6045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13330 (p : Pattern) (ha : d6817 p = 1) (hb : d70145 p = 1) : d6046 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d4826 q = 1) : d4826 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6806 q = 1) (hb : d70145 q = 1) : d4827 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6806, d70145, d4827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6806, d70145, d4827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6807 q = 1) (hb : d70145 q = 1) : d4828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6807, d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6807, d4828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6808 q = 1) (hb : d70145 q = 1) : d4829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6808, d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6808, d4829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6817 q = 1) (hb : d70145 q = 1) : d6046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6817, d6046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6817, d6046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13331 (p : Pattern) (ha : d70145 p = 1) (hb : d82076 p = 1) : d76869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d70145 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d70145 q = 1) : d6011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d6011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7837 q ha hb
    | true =>
      simp only [d515, d6011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d70145 q = 1) : d6012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d6012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d6012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d70145 q = 1) : d6013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d6013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d70145 q = 1) : d6014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d6014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d70145 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d70145 q = 1) : d6018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d6018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7838 q ha hb
    | true =>
      simp only [d525, d6018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d70145 q = 1) : d6019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d6019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d6019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d70145 q = 1) : d6020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d6020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6810 q = 1) (hb : d70145 q = 1) : d6025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6810, d6025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13327 q ha hb
    | true =>
      simp only [d6810, d6025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13325 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82067 q = 1) : d76860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82067, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82067, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d70145 q = 1) : d5401 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82068 q = 1) : d76861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82068, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82068, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82069 q = 1) : d76862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82069, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82069, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82070 q = 1) : d76863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82070, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82070, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d610 q = 1) (hb : d70145 q = 1) : d610 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d611 q = 1) (hb : d70145 q = 1) : d6037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d6037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7840 q ha hb
    | true =>
      simp only [d611, d6037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d612 q = 1) (hb : d70145 q = 1) : d6038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d6038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d6038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d613 q = 1) (hb : d70145 q = 1) : d6039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d6039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d613, d6039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d614 q = 1) (hb : d70145 q = 1) : d6040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d6040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d6040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d616 q = 1) (hb : d70145 q = 1) : d616 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d617 q = 1) (hb : d70145 q = 1) : d6042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d6042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7841 q ha hb
    | true =>
      simp only [d617, d6042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d618 q = 1) (hb : d70145 q = 1) : d6043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d6043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d6043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d619 q = 1) (hb : d70145 q = 1) : d6044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d6044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d619, d6044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6818 q = 1) (hb : d70145 q = 1) : d6047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6818, d6047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13329 q ha hb
    | true =>
      simp only [d6818, d6047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13330 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82072 q = 1) : d76865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82072, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82072, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d5408 q = 1) (hb : d70145 q = 1) : d5408 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82073 q = 1) : d76866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82073, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82073, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82074 q = 1) : d76867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82074, d76867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82074, d76867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82075 q = 1) : d76868 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82075, d76868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82075, d76868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82076 q = 1) : d76869 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82076, d76869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82076, d76869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13332 (p : Pattern) (ha : d70145 p = 1) (hb : d82083 p = 1) : d76876 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6818 q = 1) (hb : d70145 q = 1) : d6047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6818, d6047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13329 q ha hb
    | true =>
      simp only [d6818, d6047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13330 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82072 q = 1) : d76865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82072, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82072, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5408 q = 1) (hb : d70145 q = 1) : d5408 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82073 q = 1) : d76866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82073, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82073, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82081 q = 1) : d76874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82081, d76874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82081, d76874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82082 q = 1) : d76875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82082, d76875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82082, d76875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82083 q = 1) : d76876 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82083, d76876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82083, d76876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13333 (p : Pattern) (ha : d6851 p = 1) (hb : d70145 p = 1) : d6077 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d672 q = 1) : d672 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6848 q = 1) (hb : d70145 q = 1) : d6074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6848, d70145, d6074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6848, d70145, d6074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6849 q = 1) (hb : d70145 q = 1) : d6075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6849, d6075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6849, d6075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6850 q = 1) (hb : d70145 q = 1) : d6076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6850, d6076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6850, d6076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6851 q = 1) (hb : d70145 q = 1) : d6077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6851, d6077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6851, d6077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13334 (p : Pattern) (ha : d6855 p = 1) (hb : d70145 p = 1) : d6090 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6086 q = 1) : d6086 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6852 q = 1) (hb : d70145 q = 1) : d6087 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6852, d70145, d6087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6852, d70145, d6087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6853 q = 1) (hb : d70145 q = 1) : d6088 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6853, d6088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6853, d6088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6854 q = 1) (hb : d70145 q = 1) : d6089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6854, d6089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6854, d6089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6855 q = 1) (hb : d70145 q = 1) : d6090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6855, d6090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6855, d6090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13335 (p : Pattern) (ha : d70145 p = 1) (hb : d82093 p = 1) : d76886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6856 q = 1) (hb : d70145 q = 1) : d6091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6856, d6091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13333 q ha hb
    | true =>
      simp only [d6856, d6091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13334 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82089 q = 1) : d76882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82089, d76882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82089, d76882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5430 q = 1) (hb : d70145 q = 1) : d5430 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82090 q = 1) : d76883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82090, d76883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82090, d76883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82091 q = 1) : d76884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82091, d76884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82091, d76884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82092 q = 1) : d76885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82092, d76885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82092, d76885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82093 q = 1) : d76886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82093, d76886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82093, d76886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13336 (p : Pattern) (ha : d70145 p = 1) (hb : d82099 p = 1) : d76892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d70145 q = 1) : d5998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d5998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d5998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13323 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d70145 q = 1) : d5999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d5999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d5999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d70145 q = 1) : d6006 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13323 q ha hb
    | true =>
      simp only [d508, d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13324 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d70145 q = 1) : d6007 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d70145 q = 1) : d6008 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d6008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d6008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82077 q = 1) : d76870 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82077, d76870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13328 q ha hb
    | true =>
      simp only [d82077, d76870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13331 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d70145 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6831 q = 1) (hb : d70145 q = 1) : d6062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6831, d6062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13326 q ha hb
    | true =>
      simp only [d6831, d6062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82078 q = 1) : d76871 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82078, d76871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82078, d76871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82079 q = 1) : d76872 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82079, d76872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82079, d76872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82080 q = 1) : d76873 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82080, d76873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82080, d76873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82084 q = 1) : d76877 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82084, d76877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82084, d76877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13332 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d70145 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82085 q = 1) : d76878 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82085, d76878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82085, d76878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82086 q = 1) : d76879 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82086, d76879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82086, d76879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82087 q = 1) : d76880 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82087, d76880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82087, d76880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82088 q = 1) : d76881 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82088, d76881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82088, d76881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82094 q = 1) : d76887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82094, d76887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82094, d76887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13335 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d70145 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82095 q = 1) : d76888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82095, d76888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82095, d76888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82096 q = 1) : d76889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82096, d76889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82096, d76889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82097 q = 1) : d76890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82097, d76890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82097, d76890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82098 q = 1) : d76891 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82098, d76891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82098, d76891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82099 q = 1) : d76892 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82099, d76892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82099, d76892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13337 (p : Pattern) (ha : d70145 p = 1) (hb : d82105 p = 1) : d76898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82100 q = 1) : d76893 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82100, d76893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82100, d76893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13336 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82101 q = 1) : d76894 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82101, d76894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82101, d76894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82102 q = 1) : d76895 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82102, d76895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82102, d76895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82103 q = 1) : d76896 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82103, d76896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82103, d76896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82104 q = 1) : d76897 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82104, d76897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82104, d76897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82105 q = 1) : d76898 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82105, d76898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82105, d76898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13338 (p : Pattern) (ha : d789 p = 1) (hb : d70145 p = 1) : d6124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d70145 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d70145 q = 1) : d6119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d6119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4491 q ha hb
    | true =>
      simp only [d784, d6119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d70145 q = 1) : d6120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d6120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d6120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d70145 q = 1) : d6121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d70145 q = 1) : d6122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d70145 q = 1) : d6123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d789 q = 1) (hb : d70145 q = 1) : d6124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d6124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d6124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13339 (p : Pattern) (ha : d799 p = 1) (hb : d70145 p = 1) : d6133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d70145 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d70145 q = 1) : d6119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d6119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4491 q ha hb
    | true =>
      simp only [d784, d6119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d70145 q = 1) : d6120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d6120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d6120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d70145 q = 1) : d6121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d6121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d70145 q = 1) : d6122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d6122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d70145 q = 1) : d6123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d6123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d70145 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d794 q = 1) (hb : d70145 q = 1) : d6128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d6128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4487 q ha hb
    | true =>
      simp only [d794, d6128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d795 q = 1) (hb : d70145 q = 1) : d6129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d6129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d6129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d796 q = 1) (hb : d70145 q = 1) : d6130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d796, d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d797 q = 1) (hb : d70145 q = 1) : d6131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d798 q = 1) (hb : d70145 q = 1) : d6132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d799 q = 1) (hb : d70145 q = 1) : d6133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d6133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d799, d6133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13340 (p : Pattern) (ha : d6887 p = 1) (hb : d70145 p = 1) : d4925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4921 q = 1) : d4921 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6884 q = 1) (hb : d70145 q = 1) : d4922 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d70145, d4922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6884, d70145, d4922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6885 q = 1) (hb : d70145 q = 1) : d4923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6885, d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6886 q = 1) (hb : d70145 q = 1) : d4924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6886, d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6887 q = 1) (hb : d70145 q = 1) : d4925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6887, d4925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6887, d4925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13341 (p : Pattern) (ha : d6908 p = 1) (hb : d70145 p = 1) : d6193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d70145 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6903 q = 1) (hb : d70145 q = 1) : d6188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6903, d6188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13340 q ha hb
    | true =>
      simp only [d6903, d6188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6904 q = 1) (hb : d70145 q = 1) : d6189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6904, d6189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6904, d6189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6905 q = 1) (hb : d70145 q = 1) : d6190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6905, d6190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6905, d6190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6906 q = 1) (hb : d70145 q = 1) : d6191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6906, d6191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6906, d6191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6907 q = 1) (hb : d70145 q = 1) : d6192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6907, d6192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6907, d6192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d70145 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6908 q = 1) (hb : d70145 q = 1) : d6193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6908, d6193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6908, d6193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13342 (p : Pattern) (ha : d6883 p = 1) (hb : d70145 p = 1) : d6152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d847 q = 1) : d847 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6879 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6880 q = 1) (hb : d70145 q = 1) : d6149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6880, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6881 q = 1) (hb : d70145 q = 1) : d6150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6881, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6882 q = 1) (hb : d70145 q = 1) : d6151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6882, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6883 q = 1) (hb : d70145 q = 1) : d6152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6883, d6152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6883, d6152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13343 (p : Pattern) (ha : d70145 p = 1) (hb : d82111 p = 1) : d76904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d70145 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d70145 q = 1) : d6139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d6139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7849 q ha hb
    | true =>
      simp only [d807, d6139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d70145 q = 1) : d6140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d6140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d6140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d70145 q = 1) : d6141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d70145 q = 1) : d6142 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d70145 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d817 q = 1) (hb : d70145 q = 1) : d6146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d6146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7850 q ha hb
    | true =>
      simp only [d817, d6146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d70145 q = 1) : d6147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d6147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d6147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d70145 q = 1) : d6148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6888 q = 1) (hb : d70145 q = 1) : d6153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d6153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13342 q ha hb
    | true =>
      simp only [d6888, d6153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13340 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82107 q = 1) : d76900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82107, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d70145 q = 1) : d6161 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82108 q = 1) : d76901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82108, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82109 q = 1) : d76902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82109, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82110 q = 1) : d76903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82110, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82111 q = 1) : d76904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82111, d76904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82111, d76904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13344 (p : Pattern) (ha : d6894 p = 1) (hb : d70145 p = 1) : d6175 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d847 q = 1) : d847 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6879 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6880 q = 1) (hb : d70145 q = 1) : d6149 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6880, d70145, d6149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6881 q = 1) (hb : d70145 q = 1) : d6150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6881, d6150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6882 q = 1) (hb : d70145 q = 1) : d6151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6882, d6151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6894 q = 1) (hb : d70145 q = 1) : d6175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6894, d6175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6894, d6175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13345 (p : Pattern) (ha : d6895 p = 1) (hb : d70145 p = 1) : d6176 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d4921 q = 1) : d4921 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6884 q = 1) (hb : d70145 q = 1) : d4922 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d70145, d4922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6884, d70145, d4922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6885 q = 1) (hb : d70145 q = 1) : d4923 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6885, d4923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6886 q = 1) (hb : d70145 q = 1) : d4924 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6886, d4924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6895 q = 1) (hb : d70145 q = 1) : d6176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6895, d6176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6895, d6176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13346 (p : Pattern) (ha : d70145 p = 1) (hb : d82116 p = 1) : d76909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d70145 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d70145 q = 1) : d6139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d6139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7849 q ha hb
    | true =>
      simp only [d807, d6139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d70145 q = 1) : d6140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d6140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d6140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d70145 q = 1) : d6141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d6141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d70145 q = 1) : d6142 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d6142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d70145 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d817 q = 1) (hb : d70145 q = 1) : d6146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d6146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7850 q ha hb
    | true =>
      simp only [d817, d6146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d70145 q = 1) : d6147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d6147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d6147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d70145 q = 1) : d6148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d6148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6888 q = 1) (hb : d70145 q = 1) : d6153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d6153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13342 q ha hb
    | true =>
      simp only [d6888, d6153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13340 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82107 q = 1) : d76900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82107, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d70145 q = 1) : d6161 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82108 q = 1) : d76901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82108, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82109 q = 1) : d76902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82109, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82110 q = 1) : d76903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82110, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d916 q = 1) (hb : d70145 q = 1) : d916 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d917 q = 1) (hb : d70145 q = 1) : d6167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d6167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7852 q ha hb
    | true =>
      simp only [d917, d6167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d918 q = 1) (hb : d70145 q = 1) : d6168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d6168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d6168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d919 q = 1) (hb : d70145 q = 1) : d6169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d6169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d919, d6169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d920 q = 1) (hb : d70145 q = 1) : d6170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d6170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d6170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d922 q = 1) (hb : d70145 q = 1) : d922 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d923 q = 1) (hb : d70145 q = 1) : d6172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d6172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7853 q ha hb
    | true =>
      simp only [d923, d6172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d924 q = 1) (hb : d70145 q = 1) : d6173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d6173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d6173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d925 q = 1) (hb : d70145 q = 1) : d6174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d6174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d925, d6174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6896 q = 1) (hb : d70145 q = 1) : d6177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d6177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13344 q ha hb
    | true =>
      simp only [d6896, d6177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13345 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82112 q = 1) : d76905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82112, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d6182 q = 1) (hb : d70145 q = 1) : d6182 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82113 q = 1) : d76906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82113, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82114 q = 1) : d76907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82114, d76907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82114, d76907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82115 q = 1) : d76908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82115, d76908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82115, d76908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82116 q = 1) : d76909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82116, d76909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82116, d76909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13347 (p : Pattern) (ha : d70145 p = 1) (hb : d82123 p = 1) : d76916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6896 q = 1) (hb : d70145 q = 1) : d6177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d6177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13344 q ha hb
    | true =>
      simp only [d6896, d6177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13345 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82112 q = 1) : d76905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82112, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6182 q = 1) (hb : d70145 q = 1) : d6182 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82113 q = 1) : d76906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82113, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82121 q = 1) : d76914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82121, d76914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82121, d76914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82122 q = 1) : d76915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82122, d76915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82122, d76915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82123 q = 1) : d76916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d76916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82123, d76916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13348 (p : Pattern) (ha : d6929 p = 1) (hb : d70145 p = 1) : d6209 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d994 q = 1) : d994 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6926 q = 1) (hb : d70145 q = 1) : d6206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6926, d70145, d6206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6926, d70145, d6206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6927 q = 1) (hb : d70145 q = 1) : d6207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6927, d6207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6927, d6207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6928 q = 1) (hb : d70145 q = 1) : d6208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6928, d6208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6928, d6208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6929 q = 1) (hb : d70145 q = 1) : d6209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6929, d6209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6929, d6209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13349 (p : Pattern) (ha : d6933 p = 1) (hb : d70145 p = 1) : d6222 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6218 q = 1) : d6218 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6930 q = 1) (hb : d70145 q = 1) : d6219 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6930, d70145, d6219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6930, d70145, d6219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6931 q = 1) (hb : d70145 q = 1) : d6220 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6931, d6220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6931, d6220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6932 q = 1) (hb : d70145 q = 1) : d6221 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6932, d6221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6932, d6221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6933 q = 1) (hb : d70145 q = 1) : d6222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6933, d6222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6933, d6222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13350 (p : Pattern) (ha : d70145 p = 1) (hb : d82133 p = 1) : d76926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6934 q = 1) (hb : d70145 q = 1) : d6223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6934, d6223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13348 q ha hb
    | true =>
      simp only [d6934, d6223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13349 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82129 q = 1) : d76922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d76922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82129, d76922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6235 q = 1) (hb : d70145 q = 1) : d6235 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82130 q = 1) : d76923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d76923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82130, d76923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82131 q = 1) : d76924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d76924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82131, d76924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82132 q = 1) : d76925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d76925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82132, d76925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82133 q = 1) : d76926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d76926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82133, d76926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13351 (p : Pattern) (ha : d70145 p = 1) (hb : d82139 p = 1) : d76932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d70145 q = 1) : d6125 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d6125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d6125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13338 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d70145 q = 1) : d6126 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d6126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d6126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d70145 q = 1) : d6134 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13338 q ha hb
    | true =>
      simp only [d800, d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13339 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d70145 q = 1) : d6135 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d70145 q = 1) : d6136 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d6136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d6136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82117 q = 1) : d76910 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82117, d76910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13343 q ha hb
    | true =>
      simp only [d82117, d76910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13346 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d70145 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6909 q = 1) (hb : d70145 q = 1) : d6194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6909, d6194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13341 q ha hb
    | true =>
      simp only [d6909, d6194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82118 q = 1) : d76911 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82118, d76911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82118, d76911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82119 q = 1) : d76912 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d76912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82119, d76912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82120 q = 1) : d76913 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d76913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82120, d76913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82124 q = 1) : d76917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d76917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82124, d76917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13347 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d70145 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82125 q = 1) : d76918 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d76918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82125, d76918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82126 q = 1) : d76919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d76919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82126, d76919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82127 q = 1) : d76920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d76920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82127, d76920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82128 q = 1) : d76921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d76921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82128, d76921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82134 q = 1) : d76927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d76927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82134, d76927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13350 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d70145 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82135 q = 1) : d76928 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d76928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82135, d76928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82136 q = 1) : d76929 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d76929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82136, d76929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82137 q = 1) : d76930 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d76930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82137, d76930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82138 q = 1) : d76931 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d76931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82138, d76931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82139 q = 1) : d76932 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d76932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82139, d76932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13352 (p : Pattern) (ha : d70145 p = 1) (hb : d82145 p = 1) : d76938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82140 q = 1) : d76933 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d76933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82140, d76933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13351 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82141 q = 1) : d76934 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d76934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82141, d76934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82142 q = 1) : d76935 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d76935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82142, d76935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82143 q = 1) : d76936 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d76936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82143, d76936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82144 q = 1) : d76937 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d76937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82144, d76937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82145 q = 1) : d76938 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d76938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82145, d76938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13353 (p : Pattern) (ha : d1168 p = 1) (hb : d70145 p = 1) : d6263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d70145 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1163 q = 1) (hb : d70145 q = 1) : d6258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d6258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
    | true =>
      simp only [d1163, d6258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d70145 q = 1) : d6259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d6259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d6259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d70145 q = 1) : d6260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d70145 q = 1) : d6261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d70145 q = 1) : d6262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1168 q = 1) (hb : d70145 q = 1) : d6263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d6263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d6263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13354 (p : Pattern) (ha : d1178 p = 1) (hb : d70145 p = 1) : d6272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d70145 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1163 q = 1) (hb : d70145 q = 1) : d6258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d6258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4502 q ha hb
    | true =>
      simp only [d1163, d6258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d70145 q = 1) : d6259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d6259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d6259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d70145 q = 1) : d6260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d6260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d70145 q = 1) : d6261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d6261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d70145 q = 1) : d6262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d6262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d70145 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1173 q = 1) (hb : d70145 q = 1) : d6267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d6267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
    | true =>
      simp only [d1173, d6267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1174 q = 1) (hb : d70145 q = 1) : d6268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d6268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d6268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1175 q = 1) (hb : d70145 q = 1) : d6269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1175, d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1176 q = 1) (hb : d70145 q = 1) : d6270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1177 q = 1) (hb : d70145 q = 1) : d6271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1178 q = 1) (hb : d70145 q = 1) : d6272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d6272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1178, d6272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13355 (p : Pattern) (ha : d6966 p = 1) (hb : d70145 p = 1) : d5035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d5031 q = 1) : d5031 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6963 q = 1) (hb : d70145 q = 1) : d5032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d70145, d5032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6963, d70145, d5032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6964 q = 1) (hb : d70145 q = 1) : d5033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6964, d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6965 q = 1) (hb : d70145 q = 1) : d5034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6965, d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6966 q = 1) (hb : d70145 q = 1) : d5035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6966, d5035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6966, d5035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13356 (p : Pattern) (ha : d6987 p = 1) (hb : d70145 p = 1) : d6332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d70145 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6982 q = 1) (hb : d70145 q = 1) : d6327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6982, d6327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13355 q ha hb
    | true =>
      simp only [d6982, d6327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6983 q = 1) (hb : d70145 q = 1) : d6328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6983, d6328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6983, d6328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6984 q = 1) (hb : d70145 q = 1) : d6329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6984, d6329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6984, d6329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6985 q = 1) (hb : d70145 q = 1) : d6330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6985, d6330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6985, d6330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6986 q = 1) (hb : d70145 q = 1) : d6331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6986, d6331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6986, d6331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d70145 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6987 q = 1) (hb : d70145 q = 1) : d6332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6987, d6332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6987, d6332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13357 (p : Pattern) (ha : d6962 p = 1) (hb : d70145 p = 1) : d6291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1223 q = 1) : d1223 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6959 q = 1) (hb : d70145 q = 1) : d6288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d6959, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6960 q = 1) (hb : d70145 q = 1) : d6289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6960, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6961 q = 1) (hb : d70145 q = 1) : d6290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6961, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6962 q = 1) (hb : d70145 q = 1) : d6291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6962, d6291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6962, d6291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13358 (p : Pattern) (ha : d70145 p = 1) (hb : d82152 p = 1) : d76945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d70145 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d70145 q = 1) : d6278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d6278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7861 q ha hb
    | true =>
      simp only [d1186, d6278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d70145 q = 1) : d6279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d6279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d6279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d70145 q = 1) : d6280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d70145 q = 1) : d6281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d70145 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1196 q = 1) (hb : d70145 q = 1) : d6285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d6285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7862 q ha hb
    | true =>
      simp only [d1196, d6285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d70145 q = 1) : d6286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d6286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d6286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d70145 q = 1) : d6287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6967 q = 1) (hb : d70145 q = 1) : d6292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d6292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13357 q ha hb
    | true =>
      simp only [d6967, d6292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13355 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82148 q = 1) : d76941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82148, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d70145 q = 1) : d6300 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82149 q = 1) : d76942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82149, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82150 q = 1) : d76943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82150, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82151 q = 1) : d76944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82151, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82152 q = 1) : d76945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82152, d76945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82152, d76945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13359 (p : Pattern) (ha : d6973 p = 1) (hb : d70145 p = 1) : d6314 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1223 q = 1) : d1223 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6959 q = 1) (hb : d70145 q = 1) : d6288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6959, d70145, d6288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6960 q = 1) (hb : d70145 q = 1) : d6289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6960, d6289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6961 q = 1) (hb : d70145 q = 1) : d6290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6961, d6290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6973 q = 1) (hb : d70145 q = 1) : d6314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6973, d6314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6973, d6314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13360 (p : Pattern) (ha : d6974 p = 1) (hb : d70145 p = 1) : d6315 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5031 q = 1) : d5031 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6963 q = 1) (hb : d70145 q = 1) : d5032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d70145, d5032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6963, d70145, d5032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6964 q = 1) (hb : d70145 q = 1) : d5033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6964, d5033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6965 q = 1) (hb : d70145 q = 1) : d5034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6965, d5034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d6974 q = 1) (hb : d70145 q = 1) : d6315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6974, d6315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6974, d6315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13361 (p : Pattern) (ha : d70145 p = 1) (hb : d82157 p = 1) : d76950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d70145 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d70145 q = 1) : d6278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d6278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7861 q ha hb
    | true =>
      simp only [d1186, d6278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d70145 q = 1) : d6279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d6279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d6279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d70145 q = 1) : d6280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d6280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d70145 q = 1) : d6281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d6281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d70145 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1196 q = 1) (hb : d70145 q = 1) : d6285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d6285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7862 q ha hb
    | true =>
      simp only [d1196, d6285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d70145 q = 1) : d6286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d6286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d6286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d70145 q = 1) : d6287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d6287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6967 q = 1) (hb : d70145 q = 1) : d6292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d6292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13357 q ha hb
    | true =>
      simp only [d6967, d6292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13355 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82148 q = 1) : d76941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82148, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d70145 q = 1) : d6300 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82149 q = 1) : d76942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82149, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82150 q = 1) : d76943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82150, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82151 q = 1) : d76944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82151, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1327 q = 1) (hb : d70145 q = 1) : d1327 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1328 q = 1) (hb : d70145 q = 1) : d6306 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d6306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7864 q ha hb
    | true =>
      simp only [d1328, d6306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1329 q = 1) (hb : d70145 q = 1) : d6307 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d6307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d6307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1330 q = 1) (hb : d70145 q = 1) : d6308 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d6308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1330, d6308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1331 q = 1) (hb : d70145 q = 1) : d6309 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d6309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d6309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1333 q = 1) (hb : d70145 q = 1) : d1333 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1334 q = 1) (hb : d70145 q = 1) : d6311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d6311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7865 q ha hb
    | true =>
      simp only [d1334, d6311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1335 q = 1) (hb : d70145 q = 1) : d6312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d6312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d6312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1336 q = 1) (hb : d70145 q = 1) : d6313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d6313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1336, d6313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d6975 q = 1) (hb : d70145 q = 1) : d6316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d6316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13359 q ha hb
    | true =>
      simp only [d6975, d6316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13360 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82153 q = 1) : d76946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82153, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d6321 q = 1) (hb : d70145 q = 1) : d6321 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82154 q = 1) : d76947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82154, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82155 q = 1) : d76948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82155, d76948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82155, d76948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82156 q = 1) : d76949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82156, d76949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82156, d76949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82157 q = 1) : d76950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82157, d76950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82157, d76950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13362 (p : Pattern) (ha : d70145 p = 1) (hb : d82164 p = 1) : d76957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6975 q = 1) (hb : d70145 q = 1) : d6316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d6316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13359 q ha hb
    | true =>
      simp only [d6975, d6316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13360 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82153 q = 1) : d76946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82153, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6321 q = 1) (hb : d70145 q = 1) : d6321 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82154 q = 1) : d76947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82154, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82162 q = 1) : d76955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82162, d76955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82162, d76955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82163 q = 1) : d76956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82163, d76956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82163, d76956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82164 q = 1) : d76957 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d76957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82164, d76957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13363 (p : Pattern) (ha : d7008 p = 1) (hb : d70145 p = 1) : d6348 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1419 q = 1) : d1419 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7004 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7005 q = 1) (hb : d70145 q = 1) : d6345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7005, d70145, d6345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7005, d70145, d6345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7006 q = 1) (hb : d70145 q = 1) : d6346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7006, d6346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7006, d6346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7007 q = 1) (hb : d70145 q = 1) : d6347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7007, d6347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7007, d6347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7008 q = 1) (hb : d70145 q = 1) : d6348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7008, d6348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7008, d6348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13364 (p : Pattern) (ha : d7012 p = 1) (hb : d70145 p = 1) : d6367 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6363 q = 1) : d6363 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7009 q = 1) (hb : d70145 q = 1) : d6364 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7009, d70145, d6364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7009, d70145, d6364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7010 q = 1) (hb : d70145 q = 1) : d6365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7010, d6365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7010, d6365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7011 q = 1) (hb : d70145 q = 1) : d6366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7011, d6366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7011, d6366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7012 q = 1) (hb : d70145 q = 1) : d6367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7012, d6367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7012, d6367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13365 (p : Pattern) (ha : d70145 p = 1) (hb : d82174 p = 1) : d76967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7013 q = 1) (hb : d70145 q = 1) : d6368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7013, d6368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13363 q ha hb
    | true =>
      simp only [d7013, d6368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13364 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82170 q = 1) : d76963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d76963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82170, d76963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6380 q = 1) (hb : d70145 q = 1) : d6380 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82171 q = 1) : d76964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d76964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82171, d76964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82172 q = 1) : d76965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d76965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82172, d76965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82173 q = 1) : d76966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d76966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82173, d76966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82174 q = 1) : d76967 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d76967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82174, d76967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13366 (p : Pattern) (ha : d70145 p = 1) (hb : d82180 p = 1) : d76973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d70145 q = 1) : d6264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d6264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d6264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13353 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d70145 q = 1) : d6265 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d6265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d6265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d70145 q = 1) : d6273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13353 q ha hb
    | true =>
      simp only [d1179, d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13354 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d70145 q = 1) : d6274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d70145 q = 1) : d6275 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d6275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d6275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82158 q = 1) : d76951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82158, d76951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13358 q ha hb
    | true =>
      simp only [d82158, d76951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13361 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d70145 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6988 q = 1) (hb : d70145 q = 1) : d6333 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6988, d6333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13356 q ha hb
    | true =>
      simp only [d6988, d6333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82159 q = 1) : d76952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82159, d76952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82159, d76952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82160 q = 1) : d76953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d76953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82160, d76953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82161 q = 1) : d76954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d76954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82161, d76954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82165 q = 1) : d76958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d76958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82165, d76958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13362 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d70145 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82166 q = 1) : d76959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d76959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82166, d76959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82167 q = 1) : d76960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d76960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82167, d76960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82168 q = 1) : d76961 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d76961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82168, d76961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82169 q = 1) : d76962 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d76962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82169, d76962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82175 q = 1) : d76968 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d76968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82175, d76968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13365 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d70145 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82176 q = 1) : d76969 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d76969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82176, d76969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82177 q = 1) : d76970 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d76970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82177, d76970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82178 q = 1) : d76971 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d76971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82178, d76971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82179 q = 1) : d76972 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d76972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82179, d76972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82180 q = 1) : d76973 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d76973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82180, d76973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13367 (p : Pattern) (ha : d70145 p = 1) (hb : d82186 p = 1) : d76979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82181 q = 1) : d76974 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d76974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82181, d76974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13366 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82182 q = 1) : d76975 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d76975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82182, d76975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82183 q = 1) : d76976 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d76976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82183, d76976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82184 q = 1) : d76977 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d76977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82184, d76977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82185 q = 1) : d76978 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d76978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82185, d76978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82186 q = 1) : d76979 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d76979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82186, d76979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13368 (p : Pattern) (ha : d1629 p = 1) (hb : d70145 p = 1) : d6409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d70145 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1624 q = 1) (hb : d70145 q = 1) : d6404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d6404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
    | true =>
      simp only [d1624, d6404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d70145 q = 1) : d6405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d6405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d6405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d70145 q = 1) : d6406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d70145 q = 1) : d6407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d70145 q = 1) : d6408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1629 q = 1) (hb : d70145 q = 1) : d6409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d6409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d6409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13369 (p : Pattern) (ha : d1639 p = 1) (hb : d70145 p = 1) : d6418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d70145 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1624 q = 1) (hb : d70145 q = 1) : d6404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d6404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4513 q ha hb
    | true =>
      simp only [d1624, d6404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d70145 q = 1) : d6405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d6405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d6405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d70145 q = 1) : d6406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d6406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d70145 q = 1) : d6407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d6407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d70145 q = 1) : d6408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d6408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d70145 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1634 q = 1) (hb : d70145 q = 1) : d6413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d6413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
    | true =>
      simp only [d1634, d6413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1635 q = 1) (hb : d70145 q = 1) : d6414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d6414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d6414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1636 q = 1) (hb : d70145 q = 1) : d6415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1636, d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1637 q = 1) (hb : d70145 q = 1) : d6416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1638 q = 1) (hb : d70145 q = 1) : d6417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1639 q = 1) (hb : d70145 q = 1) : d6418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d6418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1639, d6418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13370 (p : Pattern) (ha : d7046 p = 1) (hb : d70145 p = 1) : d5151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d5147 q = 1) : d5147 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7043 q = 1) (hb : d70145 q = 1) : d5148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d70145, d5148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7043, d70145, d5148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7044 q = 1) (hb : d70145 q = 1) : d5149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7044, d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7045 q = 1) (hb : d70145 q = 1) : d5150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7045, d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7046 q = 1) (hb : d70145 q = 1) : d5151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7046, d5151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7046, d5151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13371 (p : Pattern) (ha : d7067 p = 1) (hb : d70145 p = 1) : d6478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d70145 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7062 q = 1) (hb : d70145 q = 1) : d6473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7062, d6473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13370 q ha hb
    | true =>
      simp only [d7062, d6473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7063 q = 1) (hb : d70145 q = 1) : d6474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7063, d6474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7063, d6474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7064 q = 1) (hb : d70145 q = 1) : d6475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7064, d6475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7064, d6475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7065 q = 1) (hb : d70145 q = 1) : d6476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7065, d6476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7065, d6476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7066 q = 1) (hb : d70145 q = 1) : d6477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7066, d6477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7066, d6477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d70145 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7067 q = 1) (hb : d70145 q = 1) : d6478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7067, d6478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7067, d6478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13372 (p : Pattern) (ha : d7042 p = 1) (hb : d70145 p = 1) : d6437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1678 q = 1) : d1678 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7038 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7039 q = 1) (hb : d70145 q = 1) : d6434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7039, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7040 q = 1) (hb : d70145 q = 1) : d6435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7040, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7041 q = 1) (hb : d70145 q = 1) : d6436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7041, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7042 q = 1) (hb : d70145 q = 1) : d6437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7042, d6437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7042, d6437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13373 (p : Pattern) (ha : d70145 p = 1) (hb : d82194 p = 1) : d76987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d70145 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d70145 q = 1) : d6424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d6424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7873 q ha hb
    | true =>
      simp only [d1647, d6424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d70145 q = 1) : d6425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d6425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d6425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d70145 q = 1) : d6426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d70145 q = 1) : d6427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d70145 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1657 q = 1) (hb : d70145 q = 1) : d6431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d6431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7874 q ha hb
    | true =>
      simp only [d1657, d6431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d70145 q = 1) : d6432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d6432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d6432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d70145 q = 1) : d6433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7047 q = 1) (hb : d70145 q = 1) : d6438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d6438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13372 q ha hb
    | true =>
      simp only [d7047, d6438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13370 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82190 q = 1) : d76983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82190, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d70145 q = 1) : d6446 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82191 q = 1) : d76984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82191, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82192 q = 1) : d76985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82192, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82193 q = 1) : d76986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82193, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82194 q = 1) : d76987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82194, d76987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82194, d76987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13374 (p : Pattern) (ha : d7053 p = 1) (hb : d70145 p = 1) : d6460 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1678 q = 1) : d1678 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7039 q = 1) (hb : d70145 q = 1) : d6434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7039, d70145, d6434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7040 q = 1) (hb : d70145 q = 1) : d6435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7040, d6435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7041 q = 1) (hb : d70145 q = 1) : d6436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7041, d6436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7053 q = 1) (hb : d70145 q = 1) : d6460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7053, d6460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7053, d6460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13375 (p : Pattern) (ha : d7054 p = 1) (hb : d70145 p = 1) : d6461 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5147 q = 1) : d5147 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7043 q = 1) (hb : d70145 q = 1) : d5148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d70145, d5148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7043, d70145, d5148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7044 q = 1) (hb : d70145 q = 1) : d5149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7044, d5149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7045 q = 1) (hb : d70145 q = 1) : d5150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7045, d5150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7054 q = 1) (hb : d70145 q = 1) : d6461 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7054, d6461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7054, d6461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13376 (p : Pattern) (ha : d70145 p = 1) (hb : d82199 p = 1) : d76992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d70145 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d70145 q = 1) : d6424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d6424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7873 q ha hb
    | true =>
      simp only [d1647, d6424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d70145 q = 1) : d6425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d6425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d6425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d70145 q = 1) : d6426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d6426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d70145 q = 1) : d6427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d6427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d70145 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1657 q = 1) (hb : d70145 q = 1) : d6431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d6431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7874 q ha hb
    | true =>
      simp only [d1657, d6431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d70145 q = 1) : d6432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d6432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d6432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d70145 q = 1) : d6433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d6433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7047 q = 1) (hb : d70145 q = 1) : d6438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d6438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13372 q ha hb
    | true =>
      simp only [d7047, d6438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13370 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82190 q = 1) : d76983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82190, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d70145 q = 1) : d6446 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82191 q = 1) : d76984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82191, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82192 q = 1) : d76985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82192, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82193 q = 1) : d76986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82193, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1804 q = 1) (hb : d70145 q = 1) : d1804 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1805 q = 1) (hb : d70145 q = 1) : d6452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d6452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7876 q ha hb
    | true =>
      simp only [d1805, d6452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1806 q = 1) (hb : d70145 q = 1) : d6453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d6453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d6453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1807 q = 1) (hb : d70145 q = 1) : d6454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d6454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1807, d6454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d1808 q = 1) (hb : d70145 q = 1) : d6455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d6455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d6455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1810 q = 1) (hb : d70145 q = 1) : d1810 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1811 q = 1) (hb : d70145 q = 1) : d6457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d6457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7877 q ha hb
    | true =>
      simp only [d1811, d6457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1812 q = 1) (hb : d70145 q = 1) : d6458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d6458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d6458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1813 q = 1) (hb : d70145 q = 1) : d6459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d6459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1813, d6459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7055 q = 1) (hb : d70145 q = 1) : d6462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d6462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13374 q ha hb
    | true =>
      simp only [d7055, d6462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13375 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82195 q = 1) : d76988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82195, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d6467 q = 1) (hb : d70145 q = 1) : d6467 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82196 q = 1) : d76989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82196, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82197 q = 1) : d76990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82197, d76990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82197, d76990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82198 q = 1) : d76991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82198, d76991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82198, d76991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82199 q = 1) : d76992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82199, d76992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82199, d76992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13377 (p : Pattern) (ha : d70145 p = 1) (hb : d82206 p = 1) : d76999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7055 q = 1) (hb : d70145 q = 1) : d6462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d6462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13374 q ha hb
    | true =>
      simp only [d7055, d6462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13375 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82195 q = 1) : d76988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82195, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6467 q = 1) (hb : d70145 q = 1) : d6467 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82196 q = 1) : d76989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82196, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82204 q = 1) : d76997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82204, d76997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82204, d76997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82205 q = 1) : d76998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82205, d76998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82205, d76998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82206 q = 1) : d76999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d76999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82206, d76999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13378 (p : Pattern) (ha : d7088 p = 1) (hb : d70145 p = 1) : d6494 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1896 q = 1) : d1896 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7085 q = 1) (hb : d70145 q = 1) : d6491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7085, d70145, d6491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7085, d70145, d6491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7086 q = 1) (hb : d70145 q = 1) : d6492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7086, d6492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7086, d6492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7087 q = 1) (hb : d70145 q = 1) : d6493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7087, d6493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7087, d6493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7088 q = 1) (hb : d70145 q = 1) : d6494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7088, d6494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7088, d6494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13379 (p : Pattern) (ha : d7092 p = 1) (hb : d70145 p = 1) : d6513 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6509 q = 1) : d6509 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7089 q = 1) (hb : d70145 q = 1) : d6510 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7089, d70145, d6510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7089, d70145, d6510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7090 q = 1) (hb : d70145 q = 1) : d6511 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7090, d6511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7090, d6511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7091 q = 1) (hb : d70145 q = 1) : d6512 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7091, d6512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7091, d6512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7092 q = 1) (hb : d70145 q = 1) : d6513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7092, d6513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7092, d6513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13380 (p : Pattern) (ha : d70145 p = 1) (hb : d82216 p = 1) : d77009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7093 q = 1) (hb : d70145 q = 1) : d6514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7093, d6514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13378 q ha hb
    | true =>
      simp only [d7093, d6514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13379 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82212 q = 1) : d77005 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d77005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82212, d77005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6526 q = 1) (hb : d70145 q = 1) : d6526 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82213 q = 1) : d77006 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d77006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82213, d77006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82214 q = 1) : d77007 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d77007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82214, d77007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82215 q = 1) : d77008 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d77008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82215, d77008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82216 q = 1) : d77009 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d77009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82216, d77009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13381 (p : Pattern) (ha : d70145 p = 1) (hb : d82222 p = 1) : d77015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d70145 q = 1) : d6410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d6410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d6410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13368 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d70145 q = 1) : d6411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d6411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d6411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d70145 q = 1) : d6419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13368 q ha hb
    | true =>
      simp only [d1640, d6419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13369 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d70145 q = 1) : d6420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d6420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d70145 q = 1) : d6421 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d6421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d6421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82200 q = 1) : d76993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82200, d76993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13373 q ha hb
    | true =>
      simp only [d82200, d76993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13376 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d70145 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7068 q = 1) (hb : d70145 q = 1) : d6479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7068, d6479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13371 q ha hb
    | true =>
      simp only [d7068, d6479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82201 q = 1) : d76994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82201, d76994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82201, d76994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82202 q = 1) : d76995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d76995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82202, d76995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82203 q = 1) : d76996 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d76996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82203, d76996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82207 q = 1) : d77000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d77000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82207, d77000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13377 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d70145 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82208 q = 1) : d77001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d77001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82208, d77001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82209 q = 1) : d77002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d77002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82209, d77002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82210 q = 1) : d77003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d77003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82210, d77003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82211 q = 1) : d77004 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d77004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82211, d77004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82217 q = 1) : d77010 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d77010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82217, d77010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13380 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d70145 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82218 q = 1) : d77011 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d77011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82218, d77011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82219 q = 1) : d77012 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d77012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82219, d77012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82220 q = 1) : d77013 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d77013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82220, d77013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82221 q = 1) : d77014 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d77014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82221, d77014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82222 q = 1) : d77015 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d77015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82222, d77015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13382 (p : Pattern) (ha : d70145 p = 1) (hb : d82228 p = 1) : d77021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82223 q = 1) : d77016 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d77016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82223, d77016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13381 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82224 q = 1) : d77017 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d77017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82224, d77017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82225 q = 1) : d77018 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d77018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82225, d77018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82226 q = 1) : d77019 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d77019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82226, d77019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82227 q = 1) : d77020 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d77020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82227, d77020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82228 q = 1) : d77021 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d77021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82228, d77021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13383 (p : Pattern) (ha : d2112 p = 1) (hb : d70145 p = 1) : d6556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d70145 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2107 q = 1) (hb : d70145 q = 1) : d6551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d6551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
    | true =>
      simp only [d2107, d6551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d70145 q = 1) : d6552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d6552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d6552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d70145 q = 1) : d6553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d70145 q = 1) : d6554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d70145 q = 1) : d6555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2112 q = 1) (hb : d70145 q = 1) : d6556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d6556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d6556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13384 (p : Pattern) (ha : d2122 p = 1) (hb : d70145 p = 1) : d6565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d70145 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2107 q = 1) (hb : d70145 q = 1) : d6551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d6551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4524 q ha hb
    | true =>
      simp only [d2107, d6551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d70145 q = 1) : d6552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d6552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d6552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d70145 q = 1) : d6553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d6553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d70145 q = 1) : d6554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d6554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d70145 q = 1) : d6555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d6555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d70145 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2117 q = 1) (hb : d70145 q = 1) : d6560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d6560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4520 q ha hb
    | true =>
      simp only [d2117, d6560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2118 q = 1) (hb : d70145 q = 1) : d6561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d6561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d6561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2119 q = 1) (hb : d70145 q = 1) : d6562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2119, d6562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2120 q = 1) (hb : d70145 q = 1) : d6563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d6563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2121 q = 1) (hb : d70145 q = 1) : d6564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d6564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2122 q = 1) (hb : d70145 q = 1) : d6565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d6565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2122, d6565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro13385 (p : Pattern) (ha : d7127 p = 1) (hb : d70145 p = 1) : d5264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d5260 q = 1) : d5260 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7124 q = 1) (hb : d70145 q = 1) : d5261 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d70145, d5261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7124, d70145, d5261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7125 q = 1) (hb : d70145 q = 1) : d5262 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7125, d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7126 q = 1) (hb : d70145 q = 1) : d5263 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7126, d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7127 q = 1) (hb : d70145 q = 1) : d5264 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7127, d5264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7127, d5264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13386 (p : Pattern) (ha : d7148 p = 1) (hb : d70145 p = 1) : d6625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d70145 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7143 q = 1) (hb : d70145 q = 1) : d6620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7143, d6620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13385 q ha hb
    | true =>
      simp only [d7143, d6620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7144 q = 1) (hb : d70145 q = 1) : d6621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7144, d6621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7144, d6621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7145 q = 1) (hb : d70145 q = 1) : d6622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7145, d6622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7145, d6622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7146 q = 1) (hb : d70145 q = 1) : d6623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7146, d6623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7146, d6623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7147 q = 1) (hb : d70145 q = 1) : d6624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7147, d6624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7147, d6624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d70145 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7148 q = 1) (hb : d70145 q = 1) : d6625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7148, d6625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7148, d6625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro13387 (p : Pattern) (ha : d7123 p = 1) (hb : d70145 p = 1) : d6584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2157 q = 1) : d2157 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7119 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7120 q = 1) (hb : d70145 q = 1) : d6581 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7120, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7121 q = 1) (hb : d70145 q = 1) : d6582 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7121, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7122 q = 1) (hb : d70145 q = 1) : d6583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7122, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7123 q = 1) (hb : d70145 q = 1) : d6584 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7123, d6584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7123, d6584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13388 (p : Pattern) (ha : d70145 p = 1) (hb : d82237 p = 1) : d77030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d70145 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d70145 q = 1) : d6571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d6571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7885 q ha hb
    | true =>
      simp only [d2130, d6571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d70145 q = 1) : d6572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d6572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d6572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d70145 q = 1) : d6573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d70145 q = 1) : d6574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d70145 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2140 q = 1) (hb : d70145 q = 1) : d6578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d6578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7886 q ha hb
    | true =>
      simp only [d2140, d6578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d70145 q = 1) : d6579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d6579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d6579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d70145 q = 1) : d6580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7128 q = 1) (hb : d70145 q = 1) : d6585 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d6585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13387 q ha hb
    | true =>
      simp only [d7128, d6585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13385 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82233 q = 1) : d77026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82233, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d70145 q = 1) : d6593 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82234 q = 1) : d77027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82234, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82235 q = 1) : d77028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82235, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82236 q = 1) : d77029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82236, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82237 q = 1) : d77030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82237, d77030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82237, d77030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13389 (p : Pattern) (ha : d7134 p = 1) (hb : d70145 p = 1) : d6607 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2157 q = 1) : d2157 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7120 q = 1) (hb : d70145 q = 1) : d6581 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7120, d70145, d6581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7121 q = 1) (hb : d70145 q = 1) : d6582 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7121, d6582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7122 q = 1) (hb : d70145 q = 1) : d6583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7122, d6583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7134 q = 1) (hb : d70145 q = 1) : d6607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7134, d6607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7134, d6607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13390 (p : Pattern) (ha : d7135 p = 1) (hb : d70145 p = 1) : d6608 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5260 q = 1) : d5260 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7124 q = 1) (hb : d70145 q = 1) : d5261 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d70145, d5261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7124, d70145, d5261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7125 q = 1) (hb : d70145 q = 1) : d5262 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7125, d5262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7126 q = 1) (hb : d70145 q = 1) : d5263 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7126, d5263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7135 q = 1) (hb : d70145 q = 1) : d6608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7135, d6608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7135, d6608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13391 (p : Pattern) (ha : d70145 p = 1) (hb : d82242 p = 1) : d77035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d70145 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d70145 q = 1) : d6571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d6571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7885 q ha hb
    | true =>
      simp only [d2130, d6571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d70145 q = 1) : d6572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d6572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d6572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d70145 q = 1) : d6573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d6573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d70145 q = 1) : d6574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d6574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d70145 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2140 q = 1) (hb : d70145 q = 1) : d6578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d6578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7886 q ha hb
    | true =>
      simp only [d2140, d6578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d70145 q = 1) : d6579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d6579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d6579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d70145 q = 1) : d6580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d6580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7128 q = 1) (hb : d70145 q = 1) : d6585 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d6585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13387 q ha hb
    | true =>
      simp only [d7128, d6585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13385 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82233 q = 1) : d77026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d82233, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d70145 q = 1) : d6593 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82234 q = 1) : d77027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82234, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82235 q = 1) : d77028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d82235, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82236 q = 1) : d77029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82236, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2282 q = 1) (hb : d70145 q = 1) : d2282 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d2283 q = 1) (hb : d70145 q = 1) : d6599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d6599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7888 q ha hb
    | true =>
      simp only [d2283, d6599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2284 q = 1) (hb : d70145 q = 1) : d6600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d6600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d6600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2285 q = 1) (hb : d70145 q = 1) : d6601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d6601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d2285, d6601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d2286 q = 1) (hb : d70145 q = 1) : d6602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d6602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d6602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2288 q = 1) (hb : d70145 q = 1) : d2288 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d2289 q = 1) (hb : d70145 q = 1) : d6604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d6604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7889 q ha hb
    | true =>
      simp only [d2289, d6604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d2290 q = 1) (hb : d70145 q = 1) : d6605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d6605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d6605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d2291 q = 1) (hb : d70145 q = 1) : d6606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d6606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d2291, d6606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7136 q = 1) (hb : d70145 q = 1) : d6609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d6609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13389 q ha hb
    | true =>
      simp only [d7136, d6609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13390 q ha hb
  have h26 (q : Pattern) (ha : d70145 q = 1) (hb : d82238 q = 1) : d77031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d82238, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d6614 q = 1) (hb : d70145 q = 1) : d6614 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d70145 q = 1) (hb : d82239 q = 1) : d77032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82239, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d70145 q = 1) (hb : d82240 q = 1) : d77033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82240, d77033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d82240, d77033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d70145 q = 1) (hb : d82241 q = 1) : d77034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82241, d77034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d82241, d77034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d70145 q = 1) (hb : d82242 q = 1) : d77035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82242, d77035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82242, d77035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13392 (p : Pattern) (ha : d70145 p = 1) (hb : d82249 p = 1) : d77042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7136 q = 1) (hb : d70145 q = 1) : d6609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d6609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13389 q ha hb
    | true =>
      simp only [d7136, d6609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13390 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82238 q = 1) : d77031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82238, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6614 q = 1) (hb : d70145 q = 1) : d6614 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82239 q = 1) : d77032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82239, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82247 q = 1) : d77040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82247, d77040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82247, d77040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82248 q = 1) : d77041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82248, d77041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82248, d77041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82249 q = 1) : d77042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d77042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82249, d77042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13393 (p : Pattern) (ha : d7169 p = 1) (hb : d70145 p = 1) : d6641 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2374 q = 1) : d2374 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7166 q = 1) (hb : d70145 q = 1) : d6638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7166, d70145, d6638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7166, d70145, d6638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7167 q = 1) (hb : d70145 q = 1) : d6639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7167, d6639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7167, d6639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7168 q = 1) (hb : d70145 q = 1) : d6640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7168, d6640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7168, d6640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7169 q = 1) (hb : d70145 q = 1) : d6641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7169, d6641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7169, d6641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13394 (p : Pattern) (ha : d7173 p = 1) (hb : d70145 p = 1) : d6660 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d6656 q = 1) : d6656 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7170 q = 1) (hb : d70145 q = 1) : d6657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7170, d70145, d6657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7170, d70145, d6657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7171 q = 1) (hb : d70145 q = 1) : d6658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7171, d6658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7171, d6658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7172 q = 1) (hb : d70145 q = 1) : d6659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7172, d6659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7172, d6659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7173 q = 1) (hb : d70145 q = 1) : d6660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7173, d6660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7173, d6660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro13395 (p : Pattern) (ha : d70145 p = 1) (hb : d82259 p = 1) : d77052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7174 q = 1) (hb : d70145 q = 1) : d6661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7174, d6661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13393 q ha hb
    | true =>
      simp only [d7174, d6661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13394 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82255 q = 1) : d77048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d77048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82255, d77048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d6673 q = 1) (hb : d70145 q = 1) : d6673 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82256 q = 1) : d77049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d77049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82256, d77049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82257 q = 1) : d77050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d77050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82257, d77050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82258 q = 1) : d77051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d77051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82258, d77051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82259 q = 1) : d77052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d77052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82259, d77052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13396 (p : Pattern) (ha : d70145 p = 1) (hb : d82265 p = 1) : d77058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d70145 q = 1) : d6557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d6557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d6557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13383 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d70145 q = 1) : d6558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d6558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d6558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d70145 q = 1) : d6566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13383 q ha hb
    | true =>
      simp only [d2123, d6566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13384 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d70145 q = 1) : d6567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d6567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d70145 q = 1) : d6568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d6568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d6568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82243 q = 1) : d77036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82243, d77036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13388 q ha hb
    | true =>
      simp only [d82243, d77036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13391 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d70145 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7149 q = 1) (hb : d70145 q = 1) : d6626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7149, d6626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13386 q ha hb
    | true =>
      simp only [d7149, d6626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82244 q = 1) : d77037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82244, d77037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82244, d77037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82245 q = 1) : d77038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d77038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82245, d77038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82246 q = 1) : d77039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d77039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d82246, d77039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82250 q = 1) : d77043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d77043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82250, d77043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13392 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d70145 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82251 q = 1) : d77044 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d77044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82251, d77044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82252 q = 1) : d77045 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d77045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82252, d77045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82253 q = 1) : d77046 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d77046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82253, d77046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d70145 q = 1) (hb : d82254 q = 1) : d77047 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d77047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82254, d77047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d70145 q = 1) (hb : d82260 q = 1) : d77053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d77053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82260, d77053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13395 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d70145 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d70145 q = 1) (hb : d82261 q = 1) : d77054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d77054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82261, d77054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d70145 q = 1) (hb : d82262 q = 1) : d77055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d77055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82262, d77055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d70145 q = 1) (hb : d82263 q = 1) : d77056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d77056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82263, d77056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d70145 q = 1) (hb : d82264 q = 1) : d77057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d77057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82264, d77057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d70145 q = 1) (hb : d82265 q = 1) : d77058 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d77058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82265, d77058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro13397 (p : Pattern) (ha : d70145 p = 1) (hb : d82271 p = 1) : d77064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82266 q = 1) : d77059 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d77059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82266, d77059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13396 q ha hb
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82267 q = 1) : d77060 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d77060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82267, d77060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82268 q = 1) : d77061 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d77061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82268, d77061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82269 q = 1) : d77062 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d77062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82269, d77062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82270 q = 1) : d77063 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d77063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82270, d77063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82271 q = 1) : d77064 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d77064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d82271, d77064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13398 (p : Pattern) (ha : d70145 p = 1) (hb : d82277 p = 1) : d77070 p = 1 := by
  have h0 (q : Pattern) (ha : d70145 q = 1) (hb : d82106 q = 1) : d76899 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d76899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13322 q ha hb
    | true =>
      simp only [d82106, d76899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13337 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82146 q = 1) : d76939 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d76939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82146, d76939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13352 q ha hb
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82147 q = 1) : d76940 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d76940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d76940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82187 q = 1) : d76980 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d76980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82187, d76980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13367 q ha hb
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82188 q = 1) : d76981 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d76981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82188, d76981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82189 q = 1) : d76982 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d76982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d76982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70145 q = 1) (hb : d82229 q = 1) : d77022 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d77022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82229, d77022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13382 q ha hb
  have h8 (q : Pattern) (ha : d70145 q = 1) (hb : d82230 q = 1) : d77023 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d77023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82230, d77023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70145 q = 1) (hb : d82231 q = 1) : d77024 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d77024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82231, d77024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70145 q = 1) (hb : d82232 q = 1) : d77025 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d77025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d77025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d70145 q = 1) (hb : d82272 q = 1) : d77065 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d77065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82272, d77065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13397 q ha hb
  have h12 (q : Pattern) (ha : d70145 q = 1) (hb : d82273 q = 1) : d77066 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d77066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82273, d77066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70145 q = 1) (hb : d82274 q = 1) : d77067 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d77067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82274, d77067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70145 q = 1) (hb : d82275 q = 1) : d77068 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d77068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d82275, d77068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d70145 q = 1) (hb : d82276 q = 1) : d77069 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d77069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d77069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d70145 q = 1) (hb : d82277 q = 1) : d77070 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d77070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d77070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro13399 (p : Pattern) (ha : d70145 p = 1) (hb : d82283 p = 1) : d77076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82278 q = 1) : d77071 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d77071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13398 q ha hb
    | true =>
      simp only [d82278, d77071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82279 q = 1) : d77072 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d77072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d77072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82280 q = 1) : d77073 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d77073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d77073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82281 q = 1) : d77074 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d77074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d77074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82282 q = 1) : d77075 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d77075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d77075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82283 q = 1) : d77076 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d77076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d77076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13400 (p : Pattern) (ha : d70145 p = 1) (hb : d82289 p = 1) : d77082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82284 q = 1) : d77077 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d77077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13399 q ha hb
    | true =>
      simp only [d82284, d77077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82285 q = 1) : d77078 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d77078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d77078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82286 q = 1) : d77079 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d77079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d77079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82287 q = 1) : d77080 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d77080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d77080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82288 q = 1) : d77081 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d77081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d77081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82289 q = 1) : d77082 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d77082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d77082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13401 (p : Pattern) (ha : d70145 p = 1) (hb : d82295 p = 1) : d77088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82290 q = 1) : d77083 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d77083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13400 q ha hb
    | true =>
      simp only [d82290, d77083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82291 q = 1) : d77084 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d77084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d77084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82292 q = 1) : d77085 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d77085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d77085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82293 q = 1) : d77086 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d77086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d77086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82294 q = 1) : d77087 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d77087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d77087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82295 q = 1) : d77088 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d77088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d77088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13402 (p : Pattern) (ha : d70145 p = 1) (hb : d82301 p = 1) : d77094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82296 q = 1) : d77089 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d77089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13401 q ha hb
    | true =>
      simp only [d82296, d77089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82297 q = 1) : d77090 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d77090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d77090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70145 q = 1) (hb : d82298 q = 1) : d77091 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d77091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d77091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70145 q = 1) (hb : d82299 q = 1) : d77092 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d77092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d77092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70145 q = 1) (hb : d82300 q = 1) : d77093 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d77093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d77093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70145 q = 1) (hb : d82301 q = 1) : d77094 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d77094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d77094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13403 (p : Pattern) (ha : d82307 p = 1) (hb : d89600 p = 1) : d77100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70145 q = 1) (hb : d82302 q = 1) : d77095 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d77095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13402 q ha hb
    | true =>
      simp only [d82302, d77095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d70145 q = 1) (hb : d82303 q = 1) : d77096 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d77096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d77096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82304 q = 1) (hb : d89600 q = 1) : d77097 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d89600, d77097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d82304, d89600, d77097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d89600 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d82305 q = 1) (hb : d89600 q = 1) : d77098 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82305, d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82306 q = 1) (hb : d89600 q = 1) : d77099 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82306, d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d82307 q = 1) (hb : d89600 q = 1) : d77100 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82307, d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro13404 (p : Pattern) (ha : d82313 p = 1) (hb : d89600 p = 1) : d77106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d89600 q = 1) : d77101 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13403 q ha hb
    | true =>
      simp only [d82308, d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d89600 q = 1) : d77102 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d89600 q = 1) : d77103 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d89600 q = 1) : d77104 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d89600 q = 1) : d77105 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d89600 q = 1) : d77106 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13405 (p : Pattern) (ha : d82319 p = 1) (hb : d89600 p = 1) : d77112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d89600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d89600 q = 1) : d77107 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13404 q ha hb
    | true =>
      simp only [d82314, d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d89600 q = 1) : d77108 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d89600 q = 1) : d77109 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d89600 q = 1) : d77110 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d89600 q = 1) : d77111 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d89600 q = 1) : d77112 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13406 (p : Pattern) (ha : d75636 p = 1) (hb : d76787 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75632 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75632, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75632, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d75633 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75633, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75634 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75634, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75635 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75635, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75636 q = 1) (hb : d76787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75636, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75636, d76787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13407 (p : Pattern) (ha : d75642 p = 1) (hb : d76792 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d5850 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75632 q = 1) (hb : d76783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75632, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75632, d76783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d75633 q = 1) (hb : d76784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75633, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75633, d76784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75634 q = 1) (hb : d76785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75634, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75634, d76785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75635 q = 1) (hb : d76786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75635, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75635, d76786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d5856 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75638 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75638, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d75638, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d75639 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75639, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75640 q = 1) (hb : d76790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75640, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d75640, d76790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75641 q = 1) (hb : d76791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75641, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d75641, d76791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75642 q = 1) (hb : d76792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75642, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75642, d76792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13408 (p : Pattern) (ha : d75649 p = 1) (hb : d76799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5856 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75638 q = 1) (hb : d76788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75638, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75638, d76788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d75639 q = 1) (hb : d76789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75639, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75639, d76789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75647 q = 1) (hb : d76797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75647, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75647, d76797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75648 q = 1) (hb : d76798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75648, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75648, d76798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75649 q = 1) (hb : d76799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75649, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75649, d76799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13409 (p : Pattern) (ha : d75660 p = 1) (hb : d76809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5874 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5874, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
    | true =>
      simp only [d5874, d75655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75656 q = 1) (hb : d76805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75656, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75656, d76805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d75657 q = 1) (hb : d76806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75657, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75657, d76806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75658 q = 1) (hb : d76807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75658, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75658, d76807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75659 q = 1) (hb : d76808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75659, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75659, d76808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75660 q = 1) (hb : d76809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75660, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75660, d76809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13410 (p : Pattern) (ha : d75666 p = 1) (hb : d76815 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d75643 q = 1) (hb : d76793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75643, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13406 q ha hb
    | true =>
      simp only [d75643, d76793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13407 q ha hb
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
  have h8 (q : Pattern) (ha : d75644 q = 1) (hb : d76794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75644, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75644, d76794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75645 q = 1) (hb : d76795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75645, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75645, d76795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75646 q = 1) (hb : d76796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75646, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75646, d76796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75650 q = 1) (hb : d76800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75650, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75650, d76800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13408 q ha hb
  have h12 (q : Pattern) (ha : d75651 q = 1) (hb : d76801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75651, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75651, d76801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d75652 q = 1) (hb : d76802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75652, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d75652, d76802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d75653 q = 1) (hb : d76803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75653, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75653, d76803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75654 q = 1) (hb : d76804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75654, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75654, d76804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75661 q = 1) (hb : d76810 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75661, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75661, d76810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13409 q ha hb
  have h17 (q : Pattern) (ha : d75662 q = 1) (hb : d76811 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75662, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75662, d76811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d75663 q = 1) (hb : d76812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75663, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75663, d76812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d75664 q = 1) (hb : d76813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75664, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d75664, d76813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d75665 q = 1) (hb : d76814 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75665, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75665, d76814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75666 q = 1) (hb : d76815 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75666, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75666, d76815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro13411 (p : Pattern) (ha : d5895 p = 1) (hb : d75676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d75672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d75673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d75674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d75675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5895 q = 1) (hb : d75676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5895, d75676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5895, d75676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13412 (p : Pattern) (ha : d5902 p = 1) (hb : d75683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d75672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d75673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d75674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d75675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5856 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5856, d75637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d5898 q = 1) (hb : d75679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5898, d75679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5898, d75679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5899 q = 1) (hb : d75680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5899, d75680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5899, d75680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5900 q = 1) (hb : d75681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5900, d75681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5900, d75681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5901 q = 1) (hb : d75682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5901, d75682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5901, d75682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5902 q = 1) (hb : d75683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5902, d75683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5902, d75683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13413 (p : Pattern) (ha : d5952 p = 1) (hb : d75726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5850 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d5850, d75631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d5891 q = 1) (hb : d75672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5891, d75672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5892 q = 1) (hb : d75673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5892, d75673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5893 q = 1) (hb : d75674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5893, d75674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5894 q = 1) (hb : d75675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5894, d75675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d5952 q = 1) (hb : d75726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5952, d75726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5952, d75726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13414 (p : Pattern) (ha : d75708 p = 1) (hb : d76825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d75689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d75689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7909 q ha hb
    | true =>
      simp only [d5908, d75689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d75690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d75690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d75690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d75691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d75691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d75691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d75692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d75692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d75696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d75696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7910 q ha hb
    | true =>
      simp only [d5915, d75696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d75697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d75697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d75697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d75698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d75698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d75703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7501 q ha hb
    | true =>
      simp only [d5922, d75703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75704 q = 1) (hb : d76821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75704, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75705 q = 1) (hb : d76822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75705, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75706 q = 1) (hb : d76823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75706, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75707 q = 1) (hb : d76824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75707, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75708 q = 1) (hb : d76825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75708, d76825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75708, d76825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13415 (p : Pattern) (ha : d75724 p = 1) (hb : d76830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5908 q = 1) (hb : d75689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5908, d75689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7909 q ha hb
    | true =>
      simp only [d5908, d75689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d5909 q = 1) (hb : d75690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5909, d75690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5909, d75690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5910 q = 1) (hb : d75691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5910, d75691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5910, d75691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5911 q = 1) (hb : d75692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5911, d75692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5911, d75692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5915 q = 1) (hb : d75696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5915, d75696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7910 q ha hb
    | true =>
      simp only [d5915, d75696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d5916 q = 1) (hb : d75697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5916, d75697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5916, d75697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5917 q = 1) (hb : d75698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5917, d75698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5917, d75698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5922 q = 1) (hb : d75703 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5922, d75703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7501 q ha hb
    | true =>
      simp only [d5922, d75703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75631 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75704 q = 1) (hb : d76821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75704, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75704, d76821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75705 q = 1) (hb : d76822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75705, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75705, d76822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75706 q = 1) (hb : d76823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75706, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75706, d76823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75707 q = 1) (hb : d76824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75707, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75707, d76824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5934 q = 1) (hb : d75710 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5934, d75710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7912 q ha hb
    | true =>
      simp only [d5934, d75710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d5935 q = 1) (hb : d75711 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5935, d75711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5935, d75711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d5936 q = 1) (hb : d75712 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5936, d75712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5936, d75712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d5937 q = 1) (hb : d75713 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5937, d75713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5937, d75713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5939 q = 1) (hb : d75715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5939, d75715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7913 q ha hb
    | true =>
      simp only [d5939, d75715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d5940 q = 1) (hb : d75716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5940, d75716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5940, d75716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5941 q = 1) (hb : d75717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5941, d75717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5941, d75717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d5943 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d75719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7503 q ha hb
    | true =>
      simp only [d5943, d75719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75720 q = 1) (hb : d76826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d75720, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75721 q = 1) (hb : d76827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75721, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75722 q = 1) (hb : d76828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75722, d76828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d75722, d76828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75723 q = 1) (hb : d76829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75723, d76829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d75723, d76829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75724 q = 1) (hb : d76830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75724, d76830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75724, d76830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13416 (p : Pattern) (ha : d75733 p = 1) (hb : d76837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5943 q = 1) (hb : d75719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5943, d75719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7503 q ha hb
    | true =>
      simp only [d5943, d75719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75720 q = 1) (hb : d76826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75720, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75720, d76826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75721 q = 1) (hb : d76827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75721, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75721, d76827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75731 q = 1) (hb : d76835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75731, d76835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75731, d76835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75732 q = 1) (hb : d76836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75732, d76836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75732, d76836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75733 q = 1) (hb : d76837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75733, d76837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75733, d76837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13417 (p : Pattern) (ha : d75748 p = 1) (hb : d76847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5969 q = 1) (hb : d75743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5969, d75743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7506 q ha hb
    | true =>
      simp only [d5969, d75743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75655 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75744 q = 1) (hb : d76843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75744, d76843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75744, d76843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5378 q = 1) (hb : d74104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7498 q ha hb
    | true =>
      simp only [d5378, d74104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5379 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5379, d74105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75745 q = 1) (hb : d76844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75745, d76844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75745, d76844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75746 q = 1) (hb : d76845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75746, d76845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75746, d76845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75747 q = 1) (hb : d76846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75747, d76846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75747, d76846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75748 q = 1) (hb : d76847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75748, d76847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75748, d76847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13418 (p : Pattern) (ha : d75754 p = 1) (hb : d76853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5896 q = 1) (hb : d75677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5896, d75677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5896, d75677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13411 q ha hb
  have h2 (q : Pattern) (ha : d5897 q = 1) (hb : d75678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5897, d75678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5897, d75678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5903 q = 1) (hb : d75684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5903, d75684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13411 q ha hb
    | true =>
      simp only [d5903, d75684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13412 q ha hb
  have h4 (q : Pattern) (ha : d5904 q = 1) (hb : d75685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5904, d75685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5904, d75685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5905 q = 1) (hb : d75686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d5905, d75686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5905, d75686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75725 q = 1) (hb : d76831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75725, d76831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13414 q ha hb
    | true =>
      simp only [d75725, d76831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13415 q ha hb
  have h7 (q : Pattern) (ha : d5953 q = 1) (hb : d75727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5953, d75727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13413 q ha hb
    | true =>
      simp only [d5953, d75727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d75728 q = 1) (hb : d76832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75728, d76832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75728, d76832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75729 q = 1) (hb : d76833 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75729, d76833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75729, d76833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75730 q = 1) (hb : d76834 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75730, d76834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75730, d76834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75734 q = 1) (hb : d76838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75734, d76838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75734, d76838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13416 q ha hb
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
  have h13 (q : Pattern) (ha : d75735 q = 1) (hb : d76839 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75735, d76839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75735, d76839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75736 q = 1) (hb : d76840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75736, d76840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75736, d76840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75737 q = 1) (hb : d76841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75737, d76841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75737, d76841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75738 q = 1) (hb : d76842 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75738, d76842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75738, d76842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75749 q = 1) (hb : d76848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75749, d76848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75749, d76848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13417 q ha hb
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
  have h19 (q : Pattern) (ha : d75750 q = 1) (hb : d76849 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75750, d76849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75750, d76849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75751 q = 1) (hb : d76850 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75751, d76850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75751, d76850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75752 q = 1) (hb : d76851 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75752, d76851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75752, d76851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75753 q = 1) (hb : d76852 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75753, d76852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75753, d76852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75754 q = 1) (hb : d76853 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75754, d76853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75754, d76853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13419 (p : Pattern) (ha : d75760 p = 1) (hb : d76859 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d75667 q = 1) (hb : d76816 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75667, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75667, d76816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13410 q ha hb
  have h6 (q : Pattern) (ha : d75668 q = 1) (hb : d76817 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75668, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75668, d76817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75669 q = 1) (hb : d76818 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75669, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75669, d76818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75670 q = 1) (hb : d76819 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75670, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75670, d76819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75671 q = 1) (hb : d76820 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75671, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75671, d76820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75755 q = 1) (hb : d76854 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75755, d76854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75755, d76854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13418 q ha hb
  have h11 (q : Pattern) (ha : d75756 q = 1) (hb : d76855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75756, d76855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75756, d76855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d75757 q = 1) (hb : d76856 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75757, d76856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75757, d76856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d75758 q = 1) (hb : d76857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75758, d76857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75758, d76857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d75759 q = 1) (hb : d76858 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75759, d76858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75759, d76858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75760 q = 1) (hb : d76859 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75760, d76859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d75760, d76859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13420 (p : Pattern) (ha : d5997 p = 1) (hb : d75766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5992, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d75762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d75762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d75762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d75763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d75763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d75763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d75764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d75764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d75764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d75765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d75765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d75765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5997 q = 1) (hb : d75766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5997, d75766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5997, d75766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13421 (p : Pattern) (ha : d6005 p = 1) (hb : d75774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5992 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5992, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5992, d75761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d5993 q = 1) (hb : d75762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5993, d75762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5993, d75762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5994 q = 1) (hb : d75763 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5994, d75763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5994, d75763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5995 q = 1) (hb : d75764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5995, d75764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5995, d75764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5996 q = 1) (hb : d75765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5996, d75765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5996, d75765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6000 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6000, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d6000, d75769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h7 (q : Pattern) (ha : d6001 q = 1) (hb : d75770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6001, d75770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6001, d75770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6002 q = 1) (hb : d75771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6002, d75771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6002, d75771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6003 q = 1) (hb : d75772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6003, d75772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6003, d75772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6004 q = 1) (hb : d75773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6004, d75773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6004, d75773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6005 q = 1) (hb : d75774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6005, d75774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6005, d75774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13422 (p : Pattern) (ha : d6061 p = 1) (hb : d75823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6056 q = 1) (hb : d75818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6056, d75818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7919 q ha hb
    | true =>
      simp only [d6056, d75818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d6057 q = 1) (hb : d75819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6057, d75819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6057, d75819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6058 q = 1) (hb : d75820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6058, d75820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6058, d75820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6059 q = 1) (hb : d75821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6059, d75821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6059, d75821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6060 q = 1) (hb : d75822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6060, d75822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6060, d75822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6061 q = 1) (hb : d75823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6061, d75823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6061, d75823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13423 (p : Pattern) (ha : d75799 p = 1) (hb : d76864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d75780 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d75780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7923 q ha hb
    | true =>
      simp only [d6011, d75780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d75781 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d75781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d75781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d75782 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d75782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d75782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d75783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d75783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d75787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d75787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7924 q ha hb
    | true =>
      simp only [d6018, d75787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d75788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d75788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d75788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d75789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d75789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d75794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7511 q ha hb
    | true =>
      simp only [d6025, d75794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7919 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75795 q = 1) (hb : d76860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75795, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d5400 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75796 q = 1) (hb : d76861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75796, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75797 q = 1) (hb : d76862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75797, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75798 q = 1) (hb : d76863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75798, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75799 q = 1) (hb : d76864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75799, d76864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75799, d76864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13424 (p : Pattern) (ha : d6046 p = 1) (hb : d75810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7918 q ha hb
    | true =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4827 q = 1) (hb : d68923 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4827, d68923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4827, d68923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4828 q = 1) (hb : d68924 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4828, d68924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4828, d68924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4829 q = 1) (hb : d68925 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4829, d68925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4829, d68925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6046 q = 1) (hb : d75810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6046, d75810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6046, d75810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13425 (p : Pattern) (ha : d75816 p = 1) (hb : d76869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6011 q = 1) (hb : d75780 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6011, d75780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7923 q ha hb
    | true =>
      simp only [d6011, d75780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d6012 q = 1) (hb : d75781 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6012, d75781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6012, d75781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6013 q = 1) (hb : d75782 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6013, d75782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6013, d75782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6014 q = 1) (hb : d75783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6014, d75783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6014, d75783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6018 q = 1) (hb : d75787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6018, d75787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7924 q ha hb
    | true =>
      simp only [d6018, d75787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d6019 q = 1) (hb : d75788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6019, d75788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6019, d75788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6020 q = 1) (hb : d75789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6020, d75789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6020, d75789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6025 q = 1) (hb : d75794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6025, d75794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7511 q ha hb
    | true =>
      simp only [d6025, d75794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7919 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75795 q = 1) (hb : d76860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75795, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75795, d76860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d5400 q = 1) (hb : d74126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7510 q ha hb
    | true =>
      simp only [d5400, d74126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5401 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5401, d74127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75796 q = 1) (hb : d76861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75796, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75796, d76861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75797 q = 1) (hb : d76862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75797, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75797, d76862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75798 q = 1) (hb : d76863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75798, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75798, d76863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6037 q = 1) (hb : d75801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6037, d75801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7926 q ha hb
    | true =>
      simp only [d6037, d75801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q ha hb
  have h17 (q : Pattern) (ha : d6038 q = 1) (hb : d75802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6038, d75802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6038, d75802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6039 q = 1) (hb : d75803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6039, d75803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6039, d75803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6040 q = 1) (hb : d75804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6040, d75804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6040, d75804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6042 q = 1) (hb : d75806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6042, d75806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7927 q ha hb
    | true =>
      simp only [d6042, d75806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h21 (q : Pattern) (ha : d6043 q = 1) (hb : d75807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6043, d75807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6043, d75807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6044 q = 1) (hb : d75808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6044, d75808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6044, d75808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6047 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d75811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7514 q ha hb
    | true =>
      simp only [d6047, d75811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13424 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75812 q = 1) (hb : d76865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d75812, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d5407 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d5408 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75813 q = 1) (hb : d76866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75813, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75814 q = 1) (hb : d76867 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75814, d76867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d75814, d76867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75815 q = 1) (hb : d76868 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75815, d76868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d75815, d76868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75816 q = 1) (hb : d76869 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75816, d76869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75816, d76869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13426 (p : Pattern) (ha : d75830 p = 1) (hb : d76876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6047 q = 1) (hb : d75811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6047, d75811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7514 q ha hb
    | true =>
      simp only [d6047, d75811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13424 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75769 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75812 q = 1) (hb : d76865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75812, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75812, d76865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5407 q = 1) (hb : d74133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7513 q ha hb
    | true =>
      simp only [d5407, d74133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5408 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5408, d74134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75813 q = 1) (hb : d76866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75813, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75813, d76866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75828 q = 1) (hb : d76874 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75828, d76874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75828, d76874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75829 q = 1) (hb : d76875 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75829, d76875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75829, d76875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75830 q = 1) (hb : d76876 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75830, d76876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75830, d76876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13427 (p : Pattern) (ha : d6090 p = 1) (hb : d75852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d75847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10861 q ha hb
    | true =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d75848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6087 q = 1) (hb : d75849 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6087, d75849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6087, d75849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6088 q = 1) (hb : d75850 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6088, d75850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6088, d75850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6089 q = 1) (hb : d75851 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6089, d75851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6089, d75851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6090 q = 1) (hb : d75852 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6090, d75852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6090, d75852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13428 (p : Pattern) (ha : d75859 p = 1) (hb : d76886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6091 q = 1) (hb : d75853 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6091, d75853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7518 q ha hb
    | true =>
      simp only [d6091, d75853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13427 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75855 q = 1) (hb : d76882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75855, d76882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75855, d76882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d5429 q = 1) (hb : d74155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7517 q ha hb
    | true =>
      simp only [d5429, d74155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5430 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5430, d74156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75856 q = 1) (hb : d76883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75856, d76883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75856, d76883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75857 q = 1) (hb : d76884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75857, d76884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75857, d76884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75858 q = 1) (hb : d76885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75858, d76885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75858, d76885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75859 q = 1) (hb : d76886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75859, d76886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75859, d76886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13429 (p : Pattern) (ha : d75865 p = 1) (hb : d76892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5998 q = 1) (hb : d75767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5998, d75767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5998, d75767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13420 q ha hb
  have h2 (q : Pattern) (ha : d5999 q = 1) (hb : d75768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5999, d75768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5999, d75768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6006 q = 1) (hb : d75775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6006, d75775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13420 q ha hb
    | true =>
      simp only [d6006, d75775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13421 q ha hb
  have h4 (q : Pattern) (ha : d6007 q = 1) (hb : d75776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6007, d75776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6007, d75776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6008 q = 1) (hb : d75777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6008, d75777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6008, d75777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75817 q = 1) (hb : d76870 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75817, d76870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13423 q ha hb
    | true =>
      simp only [d75817, d76870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13425 q ha hb
  have h7 (q : Pattern) (ha : d6062 q = 1) (hb : d75824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6062, d75824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13422 q ha hb
    | true =>
      simp only [d6062, d75824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h8 (q : Pattern) (ha : d75825 q = 1) (hb : d76871 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75825, d76871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75825, d76871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75826 q = 1) (hb : d76872 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75826, d76872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75826, d76872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75827 q = 1) (hb : d76873 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75827, d76873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75827, d76873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75831 q = 1) (hb : d76877 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75831, d76877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75831, d76877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13426 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d75832 q = 1) (hb : d76878 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75832, d76878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75832, d76878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75833 q = 1) (hb : d76879 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75833, d76879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75833, d76879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75834 q = 1) (hb : d76880 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75834, d76880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75834, d76880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75835 q = 1) (hb : d76881 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75835, d76881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75835, d76881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75860 q = 1) (hb : d76887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75860, d76887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75860, d76887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13428 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d75861 q = 1) (hb : d76888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75861, d76888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75861, d76888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75862 q = 1) (hb : d76889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75862, d76889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75862, d76889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75863 q = 1) (hb : d76890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75863, d76890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75863, d76890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75864 q = 1) (hb : d76891 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75864, d76891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75864, d76891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75865 q = 1) (hb : d76892 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75865, d76892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75865, d76892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13430 (p : Pattern) (ha : d75871 p = 1) (hb : d76898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75866 q = 1) (hb : d76893 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75866, d76893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75866, d76893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13429 q ha hb
  have h2 (q : Pattern) (ha : d75867 q = 1) (hb : d76894 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75867, d76894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75867, d76894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75868 q = 1) (hb : d76895 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75868, d76895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75868, d76895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75869 q = 1) (hb : d76896 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75869, d76896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75869, d76896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75870 q = 1) (hb : d76897 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75870, d76897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75870, d76897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75871 q = 1) (hb : d76898 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75871, d76898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75871, d76898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13431 (p : Pattern) (ha : d6124 p = 1) (hb : d75882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6119, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d75878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d75878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d75878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d75879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d75879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d75879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d75880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d75880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d75880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d75881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d75881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d75881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6124 q = 1) (hb : d75882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6124, d75882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6124, d75882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13432 (p : Pattern) (ha : d6133 p = 1) (hb : d75891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6119 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6119, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6119, d75877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6120 q = 1) (hb : d75878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6120, d75878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6120, d75878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6121 q = 1) (hb : d75879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6121, d75879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6121, d75879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6122 q = 1) (hb : d75880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6122, d75880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6122, d75880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6123 q = 1) (hb : d75881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6123, d75881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6123, d75881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6128 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6128, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6128, d75886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h7 (q : Pattern) (ha : d6129 q = 1) (hb : d75887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6129, d75887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6129, d75887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6130 q = 1) (hb : d75888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6130, d75888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6130, d75888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6131 q = 1) (hb : d75889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6131, d75889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6131, d75889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6132 q = 1) (hb : d75890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6132, d75890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6132, d75890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6133 q = 1) (hb : d75891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6133, d75891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6133, d75891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13433 (p : Pattern) (ha : d6193 p = 1) (hb : d75944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6188 q = 1) (hb : d75939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6188, d75939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7933 q ha hb
    | true =>
      simp only [d6188, d75939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d6189 q = 1) (hb : d75940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6189, d75940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6189, d75940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6190 q = 1) (hb : d75941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6190, d75941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6190, d75941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6191 q = 1) (hb : d75942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6191, d75942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6191, d75942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6192 q = 1) (hb : d75943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6192, d75943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6192, d75943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6193 q = 1) (hb : d75944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6193, d75944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6193, d75944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13434 (p : Pattern) (ha : d75918 p = 1) (hb : d76904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d75897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d75897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7937 q ha hb
    | true =>
      simp only [d6139, d75897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d75898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d75898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d75898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d75899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d75899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d75899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d75900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d75900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d75904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d75904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7938 q ha hb
    | true =>
      simp only [d6146, d75904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d75905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d75905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d75905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d75906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d75906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d75911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7523 q ha hb
    | true =>
      simp only [d6153, d75911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7933 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75912 q = 1) (hb : d76900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75912, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6160 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75915 q = 1) (hb : d76901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75915, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75916 q = 1) (hb : d76902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75916, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75917 q = 1) (hb : d76903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75917, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d75918 q = 1) (hb : d76904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75918, d76904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75918, d76904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13435 (p : Pattern) (ha : d6176 p = 1) (hb : d75929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7932 q ha hb
    | true =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4922 q = 1) (hb : d69015 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4922, d69015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4922, d69015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4923 q = 1) (hb : d69016 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4923, d69016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4923, d69016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4924 q = 1) (hb : d69017 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4924, d69017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4924, d69017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6176 q = 1) (hb : d75929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6176, d75929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6176, d75929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13436 (p : Pattern) (ha : d75937 p = 1) (hb : d76909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6139 q = 1) (hb : d75897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6139, d75897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7937 q ha hb
    | true =>
      simp only [d6139, d75897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d6140 q = 1) (hb : d75898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6140, d75898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6140, d75898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6141 q = 1) (hb : d75899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6141, d75899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6141, d75899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6142 q = 1) (hb : d75900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6142, d75900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6142, d75900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6146 q = 1) (hb : d75904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6146, d75904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7938 q ha hb
    | true =>
      simp only [d6146, d75904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d6147 q = 1) (hb : d75905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6147, d75905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6147, d75905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6148 q = 1) (hb : d75906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6148, d75906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6148, d75906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6153 q = 1) (hb : d75911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6153, d75911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7523 q ha hb
    | true =>
      simp only [d6153, d75911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7933 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d75877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75912 q = 1) (hb : d76900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75912, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d75912, d76900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6160 q = 1) (hb : d75913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7522 q ha hb
    | true =>
      simp only [d6160, d75913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6161 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6161, d75914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d75915 q = 1) (hb : d76901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75915, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75915, d76901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75916 q = 1) (hb : d76902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75916, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d75916, d76902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d75917 q = 1) (hb : d76903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75917, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d75917, d76903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6167 q = 1) (hb : d75920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6167, d75920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7940 q ha hb
    | true =>
      simp only [d6167, d75920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q ha hb
  have h17 (q : Pattern) (ha : d6168 q = 1) (hb : d75921 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6168, d75921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6168, d75921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6169 q = 1) (hb : d75922 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6169, d75922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6169, d75922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6170 q = 1) (hb : d75923 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6170, d75923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6170, d75923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6172 q = 1) (hb : d75925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6172, d75925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7941 q ha hb
    | true =>
      simp only [d6172, d75925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h21 (q : Pattern) (ha : d6173 q = 1) (hb : d75926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6173, d75926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6173, d75926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6174 q = 1) (hb : d75927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6174, d75927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6174, d75927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6177 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d75930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7526 q ha hb
    | true =>
      simp only [d6177, d75930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13435 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d75931 q = 1) (hb : d76905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d75931, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d6181 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6182 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d75934 q = 1) (hb : d76906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d75934, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d75935 q = 1) (hb : d76907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75935, d76907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d75935, d76907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d75936 q = 1) (hb : d76908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75936, d76908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d75936, d76908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d75937 q = 1) (hb : d76909 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75937, d76909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d75937, d76909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13437 (p : Pattern) (ha : d75951 p = 1) (hb : d76916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6177 q = 1) (hb : d75930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6177, d75930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7526 q ha hb
    | true =>
      simp only [d6177, d75930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13435 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75931 q = 1) (hb : d76905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75931, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75931, d76905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6181 q = 1) (hb : d75932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7525 q ha hb
    | true =>
      simp only [d6181, d75932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6182 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6182, d75933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75934 q = 1) (hb : d76906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75934, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75934, d76906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75949 q = 1) (hb : d76914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75949, d76914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75949, d76914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75950 q = 1) (hb : d76915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75950, d76915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75950, d76915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75951 q = 1) (hb : d76916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75951, d76916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75951, d76916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13438 (p : Pattern) (ha : d6222 p = 1) (hb : d75973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d75968 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10874 q ha hb
    | true =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6219 q = 1) (hb : d75970 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6219, d75970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6219, d75970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6220 q = 1) (hb : d75971 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6220, d75971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6220, d75971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6221 q = 1) (hb : d75972 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6221, d75972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6221, d75972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6222 q = 1) (hb : d75973 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6222, d75973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6222, d75973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13439 (p : Pattern) (ha : d75986 p = 1) (hb : d76926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6223 q = 1) (hb : d75974 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6223, d75974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7529 q ha hb
    | true =>
      simp only [d6223, d75974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13438 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d75979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d75980 q = 1) (hb : d76922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d75980, d76922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75980, d76922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6234 q = 1) (hb : d75981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7530 q ha hb
    | true =>
      simp only [d6234, d75981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6235 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6235, d75982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d75983 q = 1) (hb : d76923 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d75983, d76923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75983, d76923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75984 q = 1) (hb : d76924 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d75984, d76924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75984, d76924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75985 q = 1) (hb : d76925 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d75985, d76925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75985, d76925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75986 q = 1) (hb : d76926 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d75986, d76926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75986, d76926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13440 (p : Pattern) (ha : d75992 p = 1) (hb : d76932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6125 q = 1) (hb : d75883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6125, d75883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6125, d75883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13431 q ha hb
  have h2 (q : Pattern) (ha : d6126 q = 1) (hb : d75884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6126, d75884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6126, d75884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6134 q = 1) (hb : d75892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6134, d75892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13431 q ha hb
    | true =>
      simp only [d6134, d75892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13432 q ha hb
  have h4 (q : Pattern) (ha : d6135 q = 1) (hb : d75893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6135, d75893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6135, d75893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6136 q = 1) (hb : d75894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6136, d75894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6136, d75894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75938 q = 1) (hb : d76910 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75938, d76910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13434 q ha hb
    | true =>
      simp only [d75938, d76910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13436 q ha hb
  have h7 (q : Pattern) (ha : d6194 q = 1) (hb : d75945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6194, d75945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13433 q ha hb
    | true =>
      simp only [d6194, d75945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d75946 q = 1) (hb : d76911 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75946, d76911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75946, d76911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d75947 q = 1) (hb : d76912 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75947, d76912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75947, d76912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d75948 q = 1) (hb : d76913 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75948, d76913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d75948, d76913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d75952 q = 1) (hb : d76917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75952, d76917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75952, d76917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13437 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d75953 q = 1) (hb : d76918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75953, d76918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d75953, d76918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d75954 q = 1) (hb : d76919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75954, d76919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d75954, d76919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d75955 q = 1) (hb : d76920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75955, d76920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d75955, d76920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d75956 q = 1) (hb : d76921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75956, d76921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d75956, d76921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75987 q = 1) (hb : d76927 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d75987, d76927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75987, d76927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13439 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d75988 q = 1) (hb : d76928 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d75988, d76928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d75988, d76928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d75989 q = 1) (hb : d76929 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d75989, d76929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d75989, d76929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d75990 q = 1) (hb : d76930 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d75990, d76930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d75990, d76930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d75991 q = 1) (hb : d76931 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d75991, d76931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d75991, d76931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d75992 q = 1) (hb : d76932 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d75992, d76932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d75992, d76932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13441 (p : Pattern) (ha : d75998 p = 1) (hb : d76938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75993 q = 1) (hb : d76933 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d75993, d76933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75993, d76933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13440 q ha hb
  have h2 (q : Pattern) (ha : d75994 q = 1) (hb : d76934 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d75994, d76934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75994, d76934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d75995 q = 1) (hb : d76935 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d75995, d76935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75995, d76935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75996 q = 1) (hb : d76936 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d75996, d76936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75996, d76936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75997 q = 1) (hb : d76937 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d75997, d76937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75997, d76937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d75998 q = 1) (hb : d76938 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d75998, d76938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75998, d76938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13442 (p : Pattern) (ha : d6263 p = 1) (hb : d76010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6258, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d76006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d76006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d76006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d76007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d76007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d76007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d76008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d76008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d76008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d76009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d76009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d76009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6263 q = 1) (hb : d76010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6263, d76010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6263, d76010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13443 (p : Pattern) (ha : d6272 p = 1) (hb : d76019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6258 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6258, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6258, d76005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6259 q = 1) (hb : d76006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6259, d76006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6259, d76006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6260 q = 1) (hb : d76007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6260, d76007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6260, d76007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6261 q = 1) (hb : d76008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6261, d76008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6261, d76008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6262 q = 1) (hb : d76009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6262, d76009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6262, d76009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6267 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6267, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6267, d76014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h7 (q : Pattern) (ha : d6268 q = 1) (hb : d76015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6268, d76015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6268, d76015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6269 q = 1) (hb : d76016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6269, d76016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6269, d76016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6270 q = 1) (hb : d76017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6270, d76017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6270, d76017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6271 q = 1) (hb : d76018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6271, d76018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6271, d76018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6272 q = 1) (hb : d76019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6272, d76019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6272, d76019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13444 (p : Pattern) (ha : d6332 p = 1) (hb : d76072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6327 q = 1) (hb : d76067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6327, d76067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7950 q ha hb
    | true =>
      simp only [d6327, d76067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d6328 q = 1) (hb : d76068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6328, d76068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6328, d76068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6329 q = 1) (hb : d76069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6329, d76069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6329, d76069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6330 q = 1) (hb : d76070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6330, d76070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6330, d76070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6331 q = 1) (hb : d76071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6331, d76071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6331, d76071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6332 q = 1) (hb : d76072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6332, d76072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6332, d76072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13445 (p : Pattern) (ha : d76046 p = 1) (hb : d76945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d76025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d76025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7954 q ha hb
    | true =>
      simp only [d6278, d76025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d76026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d76026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d76026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d76027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d76027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d76027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d76028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d76028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d76032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d76032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7955 q ha hb
    | true =>
      simp only [d6285, d76032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d76033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d76033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d76033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d76034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d76034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d76039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7535 q ha hb
    | true =>
      simp only [d6292, d76039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7950 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76040 q = 1) (hb : d76941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76040, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6299 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76043 q = 1) (hb : d76942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76043, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76044 q = 1) (hb : d76943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76044, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76045 q = 1) (hb : d76944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76045, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76046 q = 1) (hb : d76945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76046, d76945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76046, d76945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13446 (p : Pattern) (ha : d6315 p = 1) (hb : d76057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7949 q ha hb
    | true =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5032 q = 1) (hb : d69122 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5032, d69122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5032, d69122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5033 q = 1) (hb : d69123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5033, d69123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5033, d69123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5034 q = 1) (hb : d69124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5034, d69124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5034, d69124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6315 q = 1) (hb : d76057 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6315, d76057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6315, d76057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13447 (p : Pattern) (ha : d76065 p = 1) (hb : d76950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6278 q = 1) (hb : d76025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6278, d76025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7954 q ha hb
    | true =>
      simp only [d6278, d76025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d6279 q = 1) (hb : d76026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6279, d76026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6279, d76026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6280 q = 1) (hb : d76027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6280, d76027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6280, d76027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6281 q = 1) (hb : d76028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6281, d76028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6281, d76028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6285 q = 1) (hb : d76032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6285, d76032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7955 q ha hb
    | true =>
      simp only [d6285, d76032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d6286 q = 1) (hb : d76033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6286, d76033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6286, d76033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6287 q = 1) (hb : d76034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6287, d76034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6287, d76034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6292 q = 1) (hb : d76039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6292, d76039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7535 q ha hb
    | true =>
      simp only [d6292, d76039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7950 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76005 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76040 q = 1) (hb : d76941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76040, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76040, d76941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6299 q = 1) (hb : d76041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7534 q ha hb
    | true =>
      simp only [d6299, d76041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6300 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6300, d76042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76043 q = 1) (hb : d76942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76043, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76043, d76942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76044 q = 1) (hb : d76943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76044, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76044, d76943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76045 q = 1) (hb : d76944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76045, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76045, d76944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6306 q = 1) (hb : d76048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6306, d76048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7957 q ha hb
    | true =>
      simp only [d6306, d76048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h17 (q : Pattern) (ha : d6307 q = 1) (hb : d76049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6307, d76049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6307, d76049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6308 q = 1) (hb : d76050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6308, d76050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6308, d76050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6309 q = 1) (hb : d76051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6309, d76051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6309, d76051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6311 q = 1) (hb : d76053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6311, d76053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7958 q ha hb
    | true =>
      simp only [d6311, d76053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h21 (q : Pattern) (ha : d6312 q = 1) (hb : d76054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6312, d76054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6312, d76054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6313 q = 1) (hb : d76055 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6313, d76055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6313, d76055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6316 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d76058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7538 q ha hb
    | true =>
      simp only [d6316, d76058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13446 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76059 q = 1) (hb : d76946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d76059, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d6320 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6321 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76062 q = 1) (hb : d76947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76062, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76063 q = 1) (hb : d76948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76063, d76948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d76063, d76948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76064 q = 1) (hb : d76949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76064, d76949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d76064, d76949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76065 q = 1) (hb : d76950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76065, d76950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76065, d76950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13448 (p : Pattern) (ha : d76079 p = 1) (hb : d76957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6316 q = 1) (hb : d76058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6316, d76058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7538 q ha hb
    | true =>
      simp only [d6316, d76058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13446 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76059 q = 1) (hb : d76946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76059, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76059, d76946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6320 q = 1) (hb : d76060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7537 q ha hb
    | true =>
      simp only [d6320, d76060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6321 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6321, d76061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76062 q = 1) (hb : d76947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76062, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76062, d76947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76077 q = 1) (hb : d76955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76077, d76955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76077, d76955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76078 q = 1) (hb : d76956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76078, d76956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76078, d76956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76079 q = 1) (hb : d76957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76079, d76957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76079, d76957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13449 (p : Pattern) (ha : d6367 p = 1) (hb : d76107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d76102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10888 q ha hb
    | true =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6364 q = 1) (hb : d76104 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6364, d76104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6364, d76104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6365 q = 1) (hb : d76105 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6365, d76105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6365, d76105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6366 q = 1) (hb : d76106 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6366, d76106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6366, d76106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6367 q = 1) (hb : d76107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6367, d76107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6367, d76107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13450 (p : Pattern) (ha : d76120 p = 1) (hb : d76967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6368 q = 1) (hb : d76108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6368, d76108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7541 q ha hb
    | true =>
      simp only [d6368, d76108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13449 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76113 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76114 q = 1) (hb : d76963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76114, d76963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76114, d76963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6379 q = 1) (hb : d76115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7542 q ha hb
    | true =>
      simp only [d6379, d76115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6380 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6380, d76116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76117 q = 1) (hb : d76964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76117, d76964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76117, d76964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76118 q = 1) (hb : d76965 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76118, d76965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76118, d76965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76119 q = 1) (hb : d76966 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76119, d76966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76119, d76966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76120 q = 1) (hb : d76967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76120, d76967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76120, d76967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13451 (p : Pattern) (ha : d76126 p = 1) (hb : d76973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6264 q = 1) (hb : d76011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6264, d76011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6264, d76011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13442 q ha hb
  have h2 (q : Pattern) (ha : d6265 q = 1) (hb : d76012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6265, d76012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6265, d76012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6273 q = 1) (hb : d76020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6273, d76020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13442 q ha hb
    | true =>
      simp only [d6273, d76020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13443 q ha hb
  have h4 (q : Pattern) (ha : d6274 q = 1) (hb : d76021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6274, d76021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6274, d76021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6275 q = 1) (hb : d76022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6275, d76022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6275, d76022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76066 q = 1) (hb : d76951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76066, d76951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13445 q ha hb
    | true =>
      simp only [d76066, d76951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13447 q ha hb
  have h7 (q : Pattern) (ha : d6333 q = 1) (hb : d76073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6333, d76073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13444 q ha hb
    | true =>
      simp only [d6333, d76073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d76074 q = 1) (hb : d76952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76074, d76952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76074, d76952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76075 q = 1) (hb : d76953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76075, d76953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76075, d76953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76076 q = 1) (hb : d76954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76076, d76954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76076, d76954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76080 q = 1) (hb : d76958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76080, d76958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76080, d76958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13448 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d76081 q = 1) (hb : d76959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76081, d76959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76081, d76959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76082 q = 1) (hb : d76960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76082, d76960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76082, d76960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76083 q = 1) (hb : d76961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76083, d76961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76083, d76961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76084 q = 1) (hb : d76962 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76084, d76962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76084, d76962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76121 q = 1) (hb : d76968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76121, d76968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76121, d76968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13450 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d76122 q = 1) (hb : d76969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76122, d76969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76122, d76969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76123 q = 1) (hb : d76970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76123, d76970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76123, d76970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76124 q = 1) (hb : d76971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76124, d76971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76124, d76971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76125 q = 1) (hb : d76972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76125, d76972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76125, d76972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76126 q = 1) (hb : d76973 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76126, d76973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76126, d76973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13452 (p : Pattern) (ha : d76132 p = 1) (hb : d76979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76127 q = 1) (hb : d76974 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76127, d76974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76127, d76974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13451 q ha hb
  have h2 (q : Pattern) (ha : d76128 q = 1) (hb : d76975 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76128, d76975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76128, d76975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76129 q = 1) (hb : d76976 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76129, d76976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76129, d76976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76130 q = 1) (hb : d76977 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76130, d76977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76130, d76977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76131 q = 1) (hb : d76978 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76131, d76978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76131, d76978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76132 q = 1) (hb : d76979 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76132, d76979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76132, d76979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13453 (p : Pattern) (ha : d6409 p = 1) (hb : d76145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6404, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d76141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d76141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d76141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d76142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d76142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d76142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d76143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d76143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d76143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d76144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d76144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d76144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6409 q = 1) (hb : d76145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6409, d76145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6409, d76145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13454 (p : Pattern) (ha : d6418 p = 1) (hb : d76154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6404 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6404, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6404, d76140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6405 q = 1) (hb : d76141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6405, d76141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6405, d76141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6406 q = 1) (hb : d76142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6406, d76142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6406, d76142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6407 q = 1) (hb : d76143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6407, d76143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6407, d76143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6408 q = 1) (hb : d76144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6408, d76144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6408, d76144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6413 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6413, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6413, d76149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h7 (q : Pattern) (ha : d6414 q = 1) (hb : d76150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6414, d76150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6414, d76150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6415 q = 1) (hb : d76151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6415, d76151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6415, d76151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6416 q = 1) (hb : d76152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6416, d76152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6416, d76152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6417 q = 1) (hb : d76153 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6417, d76153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6417, d76153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6418 q = 1) (hb : d76154 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6418, d76154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6418, d76154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13455 (p : Pattern) (ha : d6478 p = 1) (hb : d76207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6473 q = 1) (hb : d76202 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6473, d76202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7967 q ha hb
    | true =>
      simp only [d6473, d76202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d6474 q = 1) (hb : d76203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6474, d76203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6474, d76203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6475 q = 1) (hb : d76204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6475, d76204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6475, d76204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6476 q = 1) (hb : d76205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6476, d76205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6476, d76205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6477 q = 1) (hb : d76206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6477, d76206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6477, d76206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6478 q = 1) (hb : d76207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6478, d76207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6478, d76207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13456 (p : Pattern) (ha : d76181 p = 1) (hb : d76987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d76160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d76160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7971 q ha hb
    | true =>
      simp only [d6424, d76160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d76161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d76161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d76161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d76162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d76162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d76162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d76163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d76163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d76167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d76167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7972 q ha hb
    | true =>
      simp only [d6431, d76167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d76168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d76168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d76168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d76169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d76169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d76174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7547 q ha hb
    | true =>
      simp only [d6438, d76174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7967 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76175 q = 1) (hb : d76983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76175, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6445 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76178 q = 1) (hb : d76984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76178, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76179 q = 1) (hb : d76985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76179, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76180 q = 1) (hb : d76986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76180, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76181 q = 1) (hb : d76987 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76181, d76987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76181, d76987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13457 (p : Pattern) (ha : d6461 p = 1) (hb : d76192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7966 q ha hb
    | true =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5148 q = 1) (hb : d69235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5148, d69235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5148, d69235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5149 q = 1) (hb : d69236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5149, d69236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5149, d69236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5150 q = 1) (hb : d69237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5150, d69237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5150, d69237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6461 q = 1) (hb : d76192 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6461, d76192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6461, d76192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13458 (p : Pattern) (ha : d76200 p = 1) (hb : d76992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6424 q = 1) (hb : d76160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6424, d76160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7971 q ha hb
    | true =>
      simp only [d6424, d76160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d6425 q = 1) (hb : d76161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6425, d76161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6425, d76161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6426 q = 1) (hb : d76162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6426, d76162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6426, d76162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6427 q = 1) (hb : d76163 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6427, d76163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6427, d76163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6431 q = 1) (hb : d76167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6431, d76167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7972 q ha hb
    | true =>
      simp only [d6431, d76167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d6432 q = 1) (hb : d76168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6432, d76168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6432, d76168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6433 q = 1) (hb : d76169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6433, d76169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6433, d76169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6438 q = 1) (hb : d76174 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6438, d76174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7547 q ha hb
    | true =>
      simp only [d6438, d76174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7967 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76140 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76175 q = 1) (hb : d76983 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76175, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76175, d76983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6445 q = 1) (hb : d76176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7546 q ha hb
    | true =>
      simp only [d6445, d76176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6446 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6446, d76177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76178 q = 1) (hb : d76984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76178, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76178, d76984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76179 q = 1) (hb : d76985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76179, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76179, d76985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76180 q = 1) (hb : d76986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76180, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76180, d76986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6452 q = 1) (hb : d76183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6452, d76183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7974 q ha hb
    | true =>
      simp only [d6452, d76183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h17 (q : Pattern) (ha : d6453 q = 1) (hb : d76184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6453, d76184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6453, d76184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6454 q = 1) (hb : d76185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6454, d76185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6454, d76185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6455 q = 1) (hb : d76186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6455, d76186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6455, d76186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6457 q = 1) (hb : d76188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6457, d76188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7975 q ha hb
    | true =>
      simp only [d6457, d76188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h21 (q : Pattern) (ha : d6458 q = 1) (hb : d76189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6458, d76189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6458, d76189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6459 q = 1) (hb : d76190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6459, d76190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6459, d76190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6462 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d76193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7550 q ha hb
    | true =>
      simp only [d6462, d76193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13457 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76194 q = 1) (hb : d76988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d76194, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d6466 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6467 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76197 q = 1) (hb : d76989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76197, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76198 q = 1) (hb : d76990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76198, d76990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d76198, d76990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76199 q = 1) (hb : d76991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76199, d76991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d76199, d76991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76200 q = 1) (hb : d76992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76200, d76992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76200, d76992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13459 (p : Pattern) (ha : d76214 p = 1) (hb : d76999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6462 q = 1) (hb : d76193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6462, d76193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7550 q ha hb
    | true =>
      simp only [d6462, d76193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13457 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76194 q = 1) (hb : d76988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76194, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76194, d76988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6466 q = 1) (hb : d76195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7549 q ha hb
    | true =>
      simp only [d6466, d76195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6467 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6467, d76196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76197 q = 1) (hb : d76989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76197, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76197, d76989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76212 q = 1) (hb : d76997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76212, d76997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76212, d76997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76213 q = 1) (hb : d76998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76213, d76998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76213, d76998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76214 q = 1) (hb : d76999 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76214, d76999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76214, d76999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13460 (p : Pattern) (ha : d6513 p = 1) (hb : d76242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d76237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10902 q ha hb
    | true =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6510 q = 1) (hb : d76239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6510, d76239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6510, d76239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6511 q = 1) (hb : d76240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6511, d76240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6511, d76240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6512 q = 1) (hb : d76241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6512, d76241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6512, d76241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6513 q = 1) (hb : d76242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6513, d76242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6513, d76242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13461 (p : Pattern) (ha : d76255 p = 1) (hb : d77009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6514 q = 1) (hb : d76243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6514, d76243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7553 q ha hb
    | true =>
      simp only [d6514, d76243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13460 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76249 q = 1) (hb : d77005 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76249, d77005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76249, d77005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6525 q = 1) (hb : d76250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7554 q ha hb
    | true =>
      simp only [d6525, d76250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6526 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6526, d76251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76252 q = 1) (hb : d77006 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76252, d77006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76252, d77006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76253 q = 1) (hb : d77007 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76253, d77007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76253, d77007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76254 q = 1) (hb : d77008 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76254, d77008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76254, d77008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76255 q = 1) (hb : d77009 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76255, d77009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76255, d77009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13462 (p : Pattern) (ha : d76261 p = 1) (hb : d77015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6410 q = 1) (hb : d76146 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6410, d76146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6410, d76146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13453 q ha hb
  have h2 (q : Pattern) (ha : d6411 q = 1) (hb : d76147 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6411, d76147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6411, d76147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6419 q = 1) (hb : d76155 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6419, d76155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13453 q ha hb
    | true =>
      simp only [d6419, d76155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13454 q ha hb
  have h4 (q : Pattern) (ha : d6420 q = 1) (hb : d76156 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6420, d76156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6420, d76156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6421 q = 1) (hb : d76157 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6421, d76157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6421, d76157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76201 q = 1) (hb : d76993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76201, d76993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13456 q ha hb
    | true =>
      simp only [d76201, d76993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13458 q ha hb
  have h7 (q : Pattern) (ha : d6479 q = 1) (hb : d76208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6479, d76208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13455 q ha hb
    | true =>
      simp only [d6479, d76208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d76209 q = 1) (hb : d76994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76209, d76994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76209, d76994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76210 q = 1) (hb : d76995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76210, d76995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76210, d76995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76211 q = 1) (hb : d76996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76211, d76996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76211, d76996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76215 q = 1) (hb : d77000 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76215, d77000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76215, d77000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13459 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d76216 q = 1) (hb : d77001 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76216, d77001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76216, d77001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76217 q = 1) (hb : d77002 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76217, d77002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76217, d77002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76218 q = 1) (hb : d77003 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76218, d77003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76218, d77003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76219 q = 1) (hb : d77004 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76219, d77004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76219, d77004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76256 q = 1) (hb : d77010 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76256, d77010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76256, d77010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13461 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d76257 q = 1) (hb : d77011 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76257, d77011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76257, d77011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76258 q = 1) (hb : d77012 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76258, d77012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76258, d77012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76259 q = 1) (hb : d77013 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76259, d77013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76259, d77013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76260 q = 1) (hb : d77014 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76260, d77014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76260, d77014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76261 q = 1) (hb : d77015 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76261, d77015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76261, d77015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13463 (p : Pattern) (ha : d76267 p = 1) (hb : d77021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76262 q = 1) (hb : d77016 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76262, d77016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76262, d77016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13462 q ha hb
  have h2 (q : Pattern) (ha : d76263 q = 1) (hb : d77017 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76263, d77017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76263, d77017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76264 q = 1) (hb : d77018 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76264, d77018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76264, d77018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76265 q = 1) (hb : d77019 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76265, d77019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76265, d77019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76266 q = 1) (hb : d77020 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76266, d77020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76266, d77020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76267 q = 1) (hb : d77021 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76267, d77021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76267, d77021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13464 (p : Pattern) (ha : d6556 p = 1) (hb : d76281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6551, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d76277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d76277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d76277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d76278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d76278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d76278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d76279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d76279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d76279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d76280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d76280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d76280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6556 q = 1) (hb : d76281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6556, d76281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6556, d76281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13465 (p : Pattern) (ha : d6565 p = 1) (hb : d76290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6551 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6551, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6551, d76276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6552 q = 1) (hb : d76277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6552, d76277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6552, d76277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6553 q = 1) (hb : d76278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6553, d76278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6553, d76278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6554 q = 1) (hb : d76279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6554, d76279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6554, d76279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6555 q = 1) (hb : d76280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6555, d76280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6555, d76280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6560 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6560, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6560, d76285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h7 (q : Pattern) (ha : d6561 q = 1) (hb : d76286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6561, d76286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6561, d76286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6562 q = 1) (hb : d76287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6562, d76287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6562, d76287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6563 q = 1) (hb : d76288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6563, d76288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6563, d76288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d6564 q = 1) (hb : d76289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6564, d76289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6564, d76289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6565 q = 1) (hb : d76290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6565, d76290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6565, d76290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13466 (p : Pattern) (ha : d6625 p = 1) (hb : d76343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6620 q = 1) (hb : d76338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6620, d76338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7983 q ha hb
    | true =>
      simp only [d6620, d76338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d6621 q = 1) (hb : d76339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6621, d76339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6621, d76339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6622 q = 1) (hb : d76340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6622, d76340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6622, d76340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6623 q = 1) (hb : d76341 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6623, d76341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6623, d76341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6624 q = 1) (hb : d76342 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6624, d76342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6624, d76342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6625 q = 1) (hb : d76343 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6625, d76343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6625, d76343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro13467 (p : Pattern) (ha : d76317 p = 1) (hb : d77030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d76296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d76296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7987 q ha hb
    | true =>
      simp only [d6571, d76296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d76297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d76297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d76297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d76298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d76298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d76298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d76299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d76299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d76303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d76303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7988 q ha hb
    | true =>
      simp only [d6578, d76303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d76304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d76304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d76304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d76305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d76305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d76310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7559 q ha hb
    | true =>
      simp only [d6585, d76310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7983 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76311 q = 1) (hb : d77026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76311, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76314 q = 1) (hb : d77027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76314, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76315 q = 1) (hb : d77028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76315, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76316 q = 1) (hb : d77029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76316, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76317 q = 1) (hb : d77030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76317, d77030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76317, d77030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro13468 (p : Pattern) (ha : d6608 p = 1) (hb : d76328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7982 q ha hb
    | true =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5261 q = 1) (hb : d69345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d69345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d69345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5262 q = 1) (hb : d69346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d69346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5262, d69346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5263 q = 1) (hb : d69347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d69347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5263, d69347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6608 q = 1) (hb : d76328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6608, d76328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6608, d76328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13469 (p : Pattern) (ha : d76336 p = 1) (hb : d77035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6571 q = 1) (hb : d76296 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6571, d76296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7987 q ha hb
    | true =>
      simp only [d6571, d76296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d6572 q = 1) (hb : d76297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6572, d76297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6572, d76297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6573 q = 1) (hb : d76298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6573, d76298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6573, d76298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6574 q = 1) (hb : d76299 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6574, d76299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6574, d76299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6578 q = 1) (hb : d76303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6578, d76303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7988 q ha hb
    | true =>
      simp only [d6578, d76303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d6579 q = 1) (hb : d76304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6579, d76304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6579, d76304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6580 q = 1) (hb : d76305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6580, d76305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6580, d76305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6585 q = 1) (hb : d76310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6585, d76310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7559 q ha hb
    | true =>
      simp only [d6585, d76310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7983 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d76276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d76311 q = 1) (hb : d77026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76311, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d76311, d77026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d76314 q = 1) (hb : d77027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76314, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76314, d77027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76315 q = 1) (hb : d77028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76315, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76315, d77028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76316 q = 1) (hb : d77029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76316, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d76316, d77029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d6599 q = 1) (hb : d76319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6599, d76319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7990 q ha hb
    | true =>
      simp only [d6599, d76319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q ha hb
  have h17 (q : Pattern) (ha : d6600 q = 1) (hb : d76320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6600, d76320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6600, d76320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d6601 q = 1) (hb : d76321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6601, d76321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d6601, d76321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d6602 q = 1) (hb : d76322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6602, d76322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6602, d76322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d6604 q = 1) (hb : d76324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6604, d76324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7991 q ha hb
    | true =>
      simp only [d6604, d76324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h21 (q : Pattern) (ha : d6605 q = 1) (hb : d76325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6605, d76325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6605, d76325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d6606 q = 1) (hb : d76326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6606, d76326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d6606, d76326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d6609 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d76329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7562 q ha hb
    | true =>
      simp only [d6609, d76329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13468 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d76330 q = 1) (hb : d77031 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d76330, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d76333 q = 1) (hb : d77032 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d76333, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d76334 q = 1) (hb : d77033 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76334, d77033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d76334, d77033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d76335 q = 1) (hb : d77034 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76335, d77034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d76335, d77034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d76336 q = 1) (hb : d77035 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76336, d77035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76336, d77035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro13470 (p : Pattern) (ha : d76350 p = 1) (hb : d77042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6609 q = 1) (hb : d76329 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6609, d76329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7562 q ha hb
    | true =>
      simp only [d6609, d76329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13468 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76330 q = 1) (hb : d77031 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76330, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76330, d77031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76333 q = 1) (hb : d77032 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76333, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76333, d77032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76348 q = 1) (hb : d77040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76348, d77040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76348, d77040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76349 q = 1) (hb : d77041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76349, d77041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76349, d77041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76350 q = 1) (hb : d77042 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76350, d77042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76350, d77042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13471 (p : Pattern) (ha : d6660 p = 1) (hb : d76378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d76373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10916 q ha hb
    | true =>
      simp only [d6655, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6657 q = 1) (hb : d76375 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6657, d76375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6657, d76375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6658 q = 1) (hb : d76376 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6658, d76376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6658, d76376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6659 q = 1) (hb : d76377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6659, d76377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6659, d76377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6660 q = 1) (hb : d76378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6660, d76378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6660, d76378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro13472 (p : Pattern) (ha : d76391 p = 1) (hb : d77052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6661 q = 1) (hb : d76379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6661, d76379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7565 q ha hb
    | true =>
      simp only [d6661, d76379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13471 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d76384 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d76385 q = 1) (hb : d77048 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76385, d77048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76385, d77048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d6672 q = 1) (hb : d76386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7566 q ha hb
    | true =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6673 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d76388 q = 1) (hb : d77049 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76388, d77049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76388, d77049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76389 q = 1) (hb : d77050 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76389, d77050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76389, d77050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76390 q = 1) (hb : d77051 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76390, d77051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76390, d77051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76391 q = 1) (hb : d77052 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76391, d77052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76391, d77052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro13473 (p : Pattern) (ha : d76397 p = 1) (hb : d77058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6557 q = 1) (hb : d76282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6557, d76282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6557, d76282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13464 q ha hb
  have h2 (q : Pattern) (ha : d6558 q = 1) (hb : d76283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6558, d76283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6558, d76283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6566 q = 1) (hb : d76291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6566, d76291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13464 q ha hb
    | true =>
      simp only [d6566, d76291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13465 q ha hb
  have h4 (q : Pattern) (ha : d6567 q = 1) (hb : d76292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d6567, d76292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6567, d76292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6568 q = 1) (hb : d76293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d6568, d76293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6568, d76293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76337 q = 1) (hb : d77036 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76337, d77036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13467 q ha hb
    | true =>
      simp only [d76337, d77036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13469 q ha hb
  have h7 (q : Pattern) (ha : d6626 q = 1) (hb : d76344 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6626, d76344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13466 q ha hb
    | true =>
      simp only [d6626, d76344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d76345 q = 1) (hb : d77037 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76345, d77037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76345, d77037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d76346 q = 1) (hb : d77038 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76346, d77038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76346, d77038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d76347 q = 1) (hb : d77039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76347, d77039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d76347, d77039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76351 q = 1) (hb : d77043 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76351, d77043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76351, d77043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13470 q ha hb
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
  have h13 (q : Pattern) (ha : d76352 q = 1) (hb : d77044 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76352, d77044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76352, d77044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76353 q = 1) (hb : d77045 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76353, d77045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76353, d77045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d76354 q = 1) (hb : d77046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76354, d77046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d76354, d77046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d76355 q = 1) (hb : d77047 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76355, d77047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76355, d77047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76392 q = 1) (hb : d77053 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76392, d77053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76392, d77053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13472 q ha hb
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
  have h19 (q : Pattern) (ha : d76393 q = 1) (hb : d77054 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d76393, d77054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d76393, d77054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d76394 q = 1) (hb : d77055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d76394, d77055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d76394, d77055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d76395 q = 1) (hb : d77056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d76395, d77056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d76395, d77056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d76396 q = 1) (hb : d77057 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d76396, d77057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d76396, d77057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d76397 q = 1) (hb : d77058 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d76397, d77058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d76397, d77058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro13474 (p : Pattern) (ha : d76403 p = 1) (hb : d77064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76398 q = 1) (hb : d77059 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d76398, d77059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76398, d77059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13473 q ha hb
  have h2 (q : Pattern) (ha : d76399 q = 1) (hb : d77060 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d76399, d77060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76399, d77060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d76400 q = 1) (hb : d77061 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d76400, d77061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76400, d77061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76401 q = 1) (hb : d77062 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d76401, d77062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76401, d77062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76402 q = 1) (hb : d77063 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d76402, d77063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76402, d77063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76403 q = 1) (hb : d77064 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d76403, d77064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76403, d77064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13475 (p : Pattern) (ha : d76409 p = 1) (hb : d77070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d75872 q = 1) (hb : d76899 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75872, d76899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13419 q ha hb
    | true =>
      simp only [d75872, d76899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13430 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75999 q = 1) (hb : d76939 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d75999, d76939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d75999, d76939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13441 q ha hb
  have h3 (q : Pattern) (ha : d76000 q = 1) (hb : d76940 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76000, d76940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76000, d76940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76133 q = 1) (hb : d76980 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76133, d76980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76133, d76980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13452 q ha hb
  have h5 (q : Pattern) (ha : d76134 q = 1) (hb : d76981 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76134, d76981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76134, d76981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76135 q = 1) (hb : d76982 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76135, d76982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76135, d76982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76268 q = 1) (hb : d77022 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76268, d77022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76268, d77022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13463 q ha hb
  have h8 (q : Pattern) (ha : d76269 q = 1) (hb : d77023 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76269, d77023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76269, d77023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76270 q = 1) (hb : d77024 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76270, d77024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76270, d77024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76271 q = 1) (hb : d77025 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76271, d77025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76271, d77025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76404 q = 1) (hb : d77065 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d76404, d77065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76404, d77065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13474 q ha hb
  have h12 (q : Pattern) (ha : d76405 q = 1) (hb : d77066 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d76405, d77066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76405, d77066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76406 q = 1) (hb : d77067 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d76406, d77067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76406, d77067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76407 q = 1) (hb : d77068 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d76407, d77068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d76407, d77068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d76408 q = 1) (hb : d77069 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d76408, d77069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d76408, d77069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d76409 q = 1) (hb : d77070 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d76409, d77070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d76409, d77070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro13476 (p : Pattern) (ha : d76415 p = 1) (hb : d77076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76410 q = 1) (hb : d77071 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d76410, d77071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13475 q ha hb
    | true =>
      simp only [d76410, d77071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76411 q = 1) (hb : d77072 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d76411, d77072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76411, d77072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76412 q = 1) (hb : d77073 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d76412, d77073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76412, d77073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76413 q = 1) (hb : d77074 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d76413, d77074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76413, d77074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76414 q = 1) (hb : d77075 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d76414, d77075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76414, d77075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76415 q = 1) (hb : d77076 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d76415, d77076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76415, d77076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13477 (p : Pattern) (ha : d76421 p = 1) (hb : d77082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76416 q = 1) (hb : d77077 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d76416, d77077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13476 q ha hb
    | true =>
      simp only [d76416, d77077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76417 q = 1) (hb : d77078 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d76417, d77078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76417, d77078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76418 q = 1) (hb : d77079 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d76418, d77079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76418, d77079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76419 q = 1) (hb : d77080 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d76419, d77080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76419, d77080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76420 q = 1) (hb : d77081 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d76420, d77081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76420, d77081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76421 q = 1) (hb : d77082 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d76421, d77082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76421, d77082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13478 (p : Pattern) (ha : d76427 p = 1) (hb : d77088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76422 q = 1) (hb : d77083 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d76422, d77083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13477 q ha hb
    | true =>
      simp only [d76422, d77083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76423 q = 1) (hb : d77084 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d76423, d77084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76423, d77084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76424 q = 1) (hb : d77085 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d76424, d77085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76424, d77085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76425 q = 1) (hb : d77086 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d76425, d77086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76425, d77086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76426 q = 1) (hb : d77087 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d76426, d77087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76426, d77087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76427 q = 1) (hb : d77088 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d76427, d77088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76427, d77088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13479 (p : Pattern) (ha : d76433 p = 1) (hb : d77094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76428 q = 1) (hb : d77089 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d76428, d77089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13478 q ha hb
    | true =>
      simp only [d76428, d77089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76429 q = 1) (hb : d77090 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d76429, d77090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76429, d77090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76430 q = 1) (hb : d77091 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d76430, d77091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76430, d77091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76431 q = 1) (hb : d77092 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d76431, d77092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76431, d77092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76432 q = 1) (hb : d77093 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d76432, d77093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76432, d77093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76433 q = 1) (hb : d77094 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d76433, d77094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76433, d77094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13480 (p : Pattern) (ha : d76439 p = 1) (hb : d77100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76434 q = 1) (hb : d77095 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d76434, d77095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13479 q ha hb
    | true =>
      simp only [d76434, d77095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76435 q = 1) (hb : d77096 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d76435, d77096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76435, d77096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76436 q = 1) (hb : d77097 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d76436, d77097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76436, d77097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76437 q = 1) (hb : d77098 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d76437, d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76437, d77098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76438 q = 1) (hb : d77099 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d76438, d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76438, d77099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76439 q = 1) (hb : d77100 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d76439, d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76439, d77100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13481 (p : Pattern) (ha : d76445 p = 1) (hb : d77106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76440 q = 1) (hb : d77101 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d76440, d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13480 q ha hb
    | true =>
      simp only [d76440, d77101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76441 q = 1) (hb : d77102 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d76441, d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76441, d77102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76442 q = 1) (hb : d77103 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d76442, d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76442, d77103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76443 q = 1) (hb : d77104 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d76443, d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76443, d77104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76444 q = 1) (hb : d77105 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d76444, d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76444, d77105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76445 q = 1) (hb : d77106 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d76445, d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76445, d77106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13482 (p : Pattern) (ha : d76451 p = 1) (hb : d77112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d76446 q = 1) (hb : d77107 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d76446, d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13481 q ha hb
    | true =>
      simp only [d76446, d77107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d76447 q = 1) (hb : d77108 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d76447, d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d76447, d77108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d76448 q = 1) (hb : d77109 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d76448, d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76448, d77109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d76449 q = 1) (hb : d77110 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d76449, d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d76449, d77110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76450 q = 1) (hb : d77111 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d76450, d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76450, d77111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d76451 q = 1) (hb : d77112 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d76451, d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76451, d77112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro13483 (p : Pattern) (ha : d53655 p = 1) (hb : d70145 p = 1) : d82697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d70145 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d70145 q = 1) : d5856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4465 q ha hb
    | true =>
      simp only [d204, d5856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d70145 q = 1) : d5898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d5898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d5898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d70145 q = 1) : d5899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d5899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d70145 q = 1) : d5900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d5900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d70145 q = 1) : d5901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d5901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d70145 q = 1) : d82697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d82697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13484 (p : Pattern) (ha : d53665 p = 1) (hb : d70145 p = 1) : d82707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d70145 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d70145 q = 1) : d5874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d5874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4467 q ha hb
    | true =>
      simp only [d244, d5874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d70145 q = 1) : d82703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d82703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d70145 q = 1) : d82704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d82704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d70145 q = 1) : d82705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d82705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d70145 q = 1) : d82706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d82706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d70145 q = 1) : d82707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d82707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13485 (p : Pattern) (ha : d53671 p = 1) (hb : d70145 p = 1) : d82713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d70145 q = 1) : d5903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13311 q ha hb
    | true =>
      simp only [d292, d5903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13312 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d70145 q = 1) : d5904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d5904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d70145 q = 1) : d82695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d82695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d70145 q = 1) : d82696 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d82696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d70145 q = 1) : d82698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d82698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13483 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d70145 q = 1) : d82699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d82699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d70145 q = 1) : d82700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d82700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d70145 q = 1) : d82701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d82701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d70145 q = 1) : d82702 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d82702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d70145 q = 1) : d82708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d82708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13484 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d70145 q = 1) : d82709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d82709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d70145 q = 1) : d82710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d82710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d70145 q = 1) : d82711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d82711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d70145 q = 1) : d82712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d82712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d70145 q = 1) : d82713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d82713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13486 (p : Pattern) (ha : d53677 p = 1) (hb : d70145 p = 1) : d82719 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d70145 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d70145 q = 1) : d82714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d82714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13485 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d70145 q = 1) : d82715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d82715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d70145 q = 1) : d82716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d82716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d70145 q = 1) : d82717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d82717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d70145 q = 1) : d82718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d82718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d70145 q = 1) : d82719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d82719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13487 (p : Pattern) (ha : d53680 p = 1) (hb : d70145 p = 1) : d82722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d70145 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d502 q = 1) (hb : d70145 q = 1) : d6000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d6000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4476 q ha hb
    | true =>
      simp only [d502, d6000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d70145 q = 1) : d6001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d6001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d6001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d70145 q = 1) : d6002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d6002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d70145 q = 1) : d6003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d6003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d70145 q = 1) : d6004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d6004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d70145 q = 1) : d82722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d82722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13488 (p : Pattern) (ha : d53691 p = 1) (hb : d70145 p = 1) : d82733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d70145 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53686 q = 1) (hb : d70145 q = 1) : d82728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d82728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4478 q ha hb
    | true =>
      simp only [d53686, d82728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53687 q = 1) (hb : d70145 q = 1) : d82729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d82729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53688 q = 1) (hb : d70145 q = 1) : d82730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53688, d82730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53689 q = 1) (hb : d70145 q = 1) : d82731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d82731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53690 q = 1) (hb : d70145 q = 1) : d82732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d82732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53691 q = 1) (hb : d70145 q = 1) : d82733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d82733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13489 (p : Pattern) (ha : d53697 p = 1) (hb : d70145 p = 1) : d82739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d70145 q = 1) : d6006 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13323 q ha hb
    | true =>
      simp only [d508, d6006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13324 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d70145 q = 1) : d6007 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d6007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d70145 q = 1) : d82720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d82720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d70145 q = 1) : d82721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d82721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d70145 q = 1) : d82723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d82723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13487 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d70145 q = 1) : d82724 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d82724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d70145 q = 1) : d82725 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d82725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d70145 q = 1) : d82726 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d82726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d70145 q = 1) : d82727 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d82727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d70145 q = 1) : d82734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d82734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13488 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d70145 q = 1) : d82735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d82735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d70145 q = 1) : d82736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d82736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d70145 q = 1) : d82737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d82737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d70145 q = 1) : d82738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d82738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d70145 q = 1) : d82739 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d82739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13490 (p : Pattern) (ha : d53703 p = 1) (hb : d70145 p = 1) : d82745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d70145 q = 1) : d82740 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d82740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13489 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d70145 q = 1) : d82741 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d82741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d70145 q = 1) : d82742 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d82742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d70145 q = 1) : d82743 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d82743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d70145 q = 1) : d82744 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d82744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d70145 q = 1) : d82745 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d82745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13491 (p : Pattern) (ha : d53707 p = 1) (hb : d70145 p = 1) : d82749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d70145 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d794 q = 1) (hb : d70145 q = 1) : d6128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d6128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4487 q ha hb
    | true =>
      simp only [d794, d6128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d70145 q = 1) : d6129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d6129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d6129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d70145 q = 1) : d6130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d6130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d70145 q = 1) : d6131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d6131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d70145 q = 1) : d6132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d6132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d70145 q = 1) : d82749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d82749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13492 (p : Pattern) (ha : d53718 p = 1) (hb : d70145 p = 1) : d82760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d70145 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53713 q = 1) (hb : d70145 q = 1) : d82755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d82755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4489 q ha hb
    | true =>
      simp only [d53713, d82755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53714 q = 1) (hb : d70145 q = 1) : d82756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d82756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53715 q = 1) (hb : d70145 q = 1) : d82757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53715, d82757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53716 q = 1) (hb : d70145 q = 1) : d82758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d82758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53717 q = 1) (hb : d70145 q = 1) : d82759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d82759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53718 q = 1) (hb : d70145 q = 1) : d82760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d82760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13493 (p : Pattern) (ha : d53724 p = 1) (hb : d70145 p = 1) : d82766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d70145 q = 1) : d6134 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13338 q ha hb
    | true =>
      simp only [d800, d6134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13339 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d70145 q = 1) : d6135 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d6135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d70145 q = 1) : d82747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d82747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d70145 q = 1) : d82748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d82748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d70145 q = 1) : d82750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d82750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13491 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d70145 q = 1) : d82751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d82751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d70145 q = 1) : d82752 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d82752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d70145 q = 1) : d82753 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d82753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d70145 q = 1) : d82754 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d82754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d70145 q = 1) : d82761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d82761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13492 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d70145 q = 1) : d82762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d82762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d70145 q = 1) : d82763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d82763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d70145 q = 1) : d82764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d82764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d70145 q = 1) : d82765 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d82765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d70145 q = 1) : d82766 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d82766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13494 (p : Pattern) (ha : d53730 p = 1) (hb : d70145 p = 1) : d82772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d70145 q = 1) : d82767 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d82767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13493 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d70145 q = 1) : d82768 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d82768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d70145 q = 1) : d82769 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d82769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d70145 q = 1) : d82770 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d82770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d70145 q = 1) : d82771 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d82771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d70145 q = 1) : d82772 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d82772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13495 (p : Pattern) (ha : d53735 p = 1) (hb : d70145 p = 1) : d82777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d70145 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1173 q = 1) (hb : d70145 q = 1) : d6267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d6267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4498 q ha hb
    | true =>
      simp only [d1173, d6267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d70145 q = 1) : d6268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d6268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d6268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d70145 q = 1) : d6269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d6269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d70145 q = 1) : d6270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d6270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d70145 q = 1) : d6271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d6271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d70145 q = 1) : d82777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d82777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13496 (p : Pattern) (ha : d53746 p = 1) (hb : d70145 p = 1) : d82788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d70145 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53741 q = 1) (hb : d70145 q = 1) : d82783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d82783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4500 q ha hb
    | true =>
      simp only [d53741, d82783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53742 q = 1) (hb : d70145 q = 1) : d82784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d82784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53743 q = 1) (hb : d70145 q = 1) : d82785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53743, d82785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53744 q = 1) (hb : d70145 q = 1) : d82786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d82786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53745 q = 1) (hb : d70145 q = 1) : d82787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d82787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53746 q = 1) (hb : d70145 q = 1) : d82788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d82788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro13497 (p : Pattern) (ha : d53752 p = 1) (hb : d70145 p = 1) : d82794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d70145 q = 1) : d6273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13353 q ha hb
    | true =>
      simp only [d1179, d6273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13354 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d70145 q = 1) : d6274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d6274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d70145 q = 1) : d82775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d82775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d70145 q = 1) : d82776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d82776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d70145 q = 1) : d82778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d82778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13495 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d70145 q = 1) : d82779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d82779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d70145 q = 1) : d82780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d82780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d70145 q = 1) : d82781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d82781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d70145 q = 1) : d82782 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d82782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d70145 q = 1) : d82789 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d82789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13496 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d70145 q = 1) : d82790 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d82790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d70145 q = 1) : d82791 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d82791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d70145 q = 1) : d82792 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d82792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d70145 q = 1) : d82793 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d82793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d70145 q = 1) : d82794 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d82794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro13498 (p : Pattern) (ha : d53758 p = 1) (hb : d70145 p = 1) : d82800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d70145 q = 1) : d82795 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d82795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13497 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d70145 q = 1) : d82796 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d82796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d70145 q = 1) : d82797 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d82797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d70145 q = 1) : d82798 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d82798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d70145 q = 1) : d82799 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d82799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d70145 q = 1) : d82800 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d82800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro13499 (p : Pattern) (ha : d53764 p = 1) (hb : d70145 p = 1) : d82806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d70145 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1634 q = 1) (hb : d70145 q = 1) : d6413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d6413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4509 q ha hb
    | true =>
      simp only [d1634, d6413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d70145 q = 1) : d6414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d6414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d6414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d70145 q = 1) : d6415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d6415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d70145 q = 1) : d6416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d6416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d70145 q = 1) : d6417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d6417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d70145 q = 1) : d82806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d82806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
